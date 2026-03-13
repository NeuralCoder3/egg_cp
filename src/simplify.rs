use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::io::{self, BufWriter, Write};
use std::str::FromStr;
use std::sync::Arc;
use std::rc::Rc;
use std::hash::{Hash, Hasher};
use std::time::{Duration, Instant};
use egg::rewrite::{SubstitutionSet, Term, all_critical_pair_ref, parse_term, subst, term_size, vars};
use egg::{Analysis, AstDepth, Condition, ConditionalApplier, Extractor, Id, Language, Pattern, RecExpr, Runner, Searcher, StopReason, Subst, Symbol, Var, define_language};
use hotpath::measure_block;
use colored::*;
use rustc_hash::FxHashSet;
use slog::info;

use crate::{Args, logger::Loggers, structs::{ExpressionStruct, ResultStructure}};


// Defining aliases to reduce code.
pub type EGraph = egg::EGraph<Math, ConstantFold>;
// pub type Rewrite = egg::Rewrite<Math, ConstantFold>;
pub type Rewrite = ConditionRewrite<Math, ConstantFold>;

//Definition of the language used.
define_language! {
    pub enum Math {
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "%" = Mod([Id; 2]),
        "max" = Max([Id; 2]),
        "min" = Min([Id; 2]),
        "<" = Lt([Id; 2]),
        ">" = Gt([Id; 2]),
        "!" = Not(Id),
        "<=" = Let([Id;2]),
        ">=" = Get([Id;2]),
        "==" = Eq([Id; 2]),
        "!=" = IEq([Id; 2]),
        "||" = Or([Id; 2]),
        "&&" = And([Id; 2]),
        Constant(i64),
        Symbol(Symbol),
    }
}
/// Enabling Constant Folding through the Analysis of egg.
#[derive(Default, Clone)]
pub struct ConstantFold;

impl Analysis<Math> for ConstantFold {
    type Data = Option<i64>;

    fn merge(&self, a: &mut Self::Data, b: Self::Data) -> Option<Ordering> {
        match (a.as_mut(), &b) {
            (None, None) => Some(Ordering::Equal),
            (None, Some(_)) => {
                *a = b;
                Some(Ordering::Less)
            }
            (Some(_), None) => Some(Ordering::Greater),
            (Some(_), Some(_)) => Some(Ordering::Equal),
        }
        // if a.is_none() && b.is_some() {
        //     *a = b
        // }
        // cmp
    }

    fn make(egraph: &EGraph, enode: &Math) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.as_ref();
        Some(match enode {
            Math::Constant(c) => *c,
            Math::Add([a, b]) => x(a)? + x(b)?,
            Math::Sub([a, b]) => x(a)? - x(b)?,
            Math::Mul([a, b]) => x(a)? * x(b)?,
            Math::Div([a, b]) if *x(b)? != 0 => x(a)? / x(b)?,
            Math::Max([a, b]) => std::cmp::max(*x(a)?, *x(b)?),
            Math::Min([a, b]) => std::cmp::min(*x(a)?, *x(b)?),
            Math::Not(a) => {
                if *x(a)? == 0 {
                    1
                } else {
                    0
                }
            }
            Math::Lt([a, b]) => {
                if x(a)? < x(b)? {
                    1
                } else {
                    0
                }
            }
            Math::Gt([a, b]) => {
                if x(a)? > x(b)? {
                    1
                } else {
                    0
                }
            }
            Math::Let([a, b]) => {
                if x(a)? <= x(b)? {
                    1
                } else {
                    0
                }
            }
            Math::Get([a, b]) => {
                if x(a)? >= x(b)? {
                    1
                } else {
                    0
                }
            }
            Math::Mod([a, b]) => {
                if *x(b)? == 0 {
                    0
                } else {
                    x(a)? % x(b)?
                }
            }
            Math::Eq([a, b]) => {
                if x(a)? == x(b)? {
                    1
                } else {
                    0
                }
            }
            Math::IEq([a, b]) => {
                if x(a)? != x(b)? {
                    1
                } else {
                    0
                }
            }
            Math::And([a, b]) => {
                if *x(a)? == 0 || *x(b)? == 0 {
                    0
                } else {
                    1
                }
            }
            Math::Or([a, b]) => {
                if *x(a)? == 1 || *x(b)? == 1 {
                    1
                } else {
                    0
                }
            }

            _ => return None,
        })
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        let class = &mut egraph[id];
        if let Some(c) = class.data.clone() {
            let added = egraph.add(Math::Constant(c.clone()));
            let (id, _did_something) = egraph.union(id, added);
            // to not prune, comment this out
            egraph[id].nodes.retain(|n| n.is_leaf());

            assert!(
                !egraph[id].nodes.is_empty(),
                "empty eclass! {:#?}",
                egraph[id]
            );
            #[cfg(debug_assertions)]
            egraph[id].assert_unique_leaves();
        }
    }
}

pub fn all_conditions_extended(
    conds: Vec<Arc<dyn ExtendedCondition<Math,ConstantFold>>>
) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, id, subst| {
        for cond in conds.iter() {
            if !cond.as_condition().check(egraph, id, subst) {
                return false;
            }
        }
        true
    }
}


// pub fn all_conditions(
//     conds: Vec<impl Fn(&mut EGraph, Id, &Subst) -> bool>
// ) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
//     move |egraph, id, subst| {
//         for cond in conds.iter() {
//             if !cond(egraph, id, subst) {
//                 return false;
//             }
//         }
//         true
//     }
// }

pub fn is_const_pos(var: &str) -> impl ExtendedCondition<Math,ConstantFold> {
    IsConstPosCondition::new(var)
}

pub fn is_const_neg(var: &str) -> impl ExtendedCondition<Math,ConstantFold> {
    IsConstNegCondition::new(var)
}

/// Checks if a constant is positive
pub fn is_const_pos_fun(var: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    // Get the constant
    // let var = var.parse().unwrap();

    // Get the substitutions where the constant appears
    move |egraph, _, subst| {
        // Check if any of the representations of ths constant (nodes inside its eclass) is positive
        egraph[subst[var]].nodes.iter().any(|n| match n {
            Math::Constant(c) => c > &0,
            _ => return false,
        })
    }
}

/// Checks if a constant is negative
pub fn is_const_neg_fun(var: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    // let var = var.parse().unwrap();

    // Get the substitutions where the constant appears
    move |egraph, _, subst| {
        //Check if any of the representations of ths constant (nodes inside its eclass) is negative
        egraph[subst[var]].nodes.iter().any(|n| match n {
            Math::Constant(c) => c < &0,
            _ => return false,
        })
    }
}

/// Checks if a constant is equals zero
pub fn is_not_zero(var: &str) -> impl ExtendedCondition<Math,ConstantFold> {
    IsNotZeroCondition::new(var)
}
// pub fn is_not_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
//     let var = var.parse().unwrap();
//     let zero = Math::Constant(0);
//     // Check if any of the representations of the constant (nodes inside its eclass) is zero
//     move |egraph, _, subst| !egraph[subst[var]].nodes.contains(&zero)
// }


pub fn is_not_zero_fun(var: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let zero = Math::Constant(0);
    // Check if any of the representations of the constant (nodes inside its eclass) is zero
    move |egraph, _, subst| !egraph[subst[var]].nodes.contains(&zero)
}

pub fn compare_c0_c1(
    // first constant
    var: &str,
    // 2nd constant
    var1: &str,
    // the comparison we're checking
    comp: &'static str,
) -> impl ExtendedCondition<Math,ConstantFold> {
    CompareC0C1Condition::new(var, var1, comp)
}




/// Compares two constants c0 and c1
pub fn compare_c0_c1_fun(
    // first constant
    var: Var,
    // 2nd constant
    var1: Var,
    // the comparison we're checking
    comp: &'static str,
) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    // Get constants
    // let var: Var = var.parse().unwrap();
    // let var1: Var = var1.parse().unwrap();

    move |egraph, _, subst| {

        if subst.get(var).is_none() {
            panic!("Variable {:?} (var1: {:?}, comp: {:?}) not found in substitution {:?}", var, var1, comp, subst);
        }
        if subst.get(var1).is_none() {
            panic!("Variable1 {:?} (var: {:?}, comp: {:?}) not found in substitution {:?}", var1, var, comp, subst);
        }

        // Get the eclass of the first constant then match the values of its enodes to check if one of them proves the coming conditions
        egraph[subst[var1]].nodes.iter().any(|n1| match n1 {
            // Get the eclass of the second constant then match it to c1
            Math::Constant(c1) => egraph[subst[var]].nodes.iter().any(|n| match n {
                // match the comparison then do it
                Math::Constant(c) => match comp {
                    "<" => c < c1,
                    "<a" => c < &c1.abs(),
                    "<=" => c <= c1,
                    "<=+1" => c <= &(c1 + 1),
                    "<=a" => c <= &c1.abs() && c1 != &0,
                    "<=-a" => c <= &(-c1.abs()) && c1 != &0,
                    "<=-a+1" => c <= &(1 - c1.abs()) && c != &0,
                    ">" => c > c1,
                    // ">a" => c > &c1.abs(),
                    ">=" => c >= c1,
                    ">=a" => c >= &(c1.abs()) && c1 != &0,
                    ">=a-1" => c >= &(c1.abs() - 1) && c1 != &0,
                    "!=" => c != c1,
                    "%0" => (*c1 != 0) && (c % c1 == 0),
                    "!%0" => (*c1 != 0) && (c % c1 != 0),
                    "%0<" => (*c1 > 0) && (c % c1 == 0),
                    "%0<0" => (*c1 > 0) && (c % c1 == 0) && (c != &0),
                    "%0>" => (*c1 < 0) && (c % c1 == 0),
                    _ => false,
                },
                _ => return false,
            }),
            _ => return false,
        })
    }
}


#[macro_export]
macro_rules! rewrite2 {
    (
        $name:expr;
        $lhs:tt => $rhs:tt
    )  => {{
        let searcher = $crate::__rewrite2!(@parse $lhs);
        let core_applier = $crate::__rewrite2!(@parse $rhs);
        let applier = core_applier;
        let rewrite = egg::Rewrite::new(
            $name,
            ($lhs).to_string(),
            ($rhs).to_string(),
            // vec![],
            // None::<std::sync::Arc<dyn egg::Condition<Math, ConstantFold>>>,
            // None,
            searcher,
            applier,
        ).unwrap();
        // let empty_cond: Vec<impl ExtendedCondition<Math, ConstantFold>> = vec![];
        $crate::simplify::ConditionRewrite::of_rewrite(
            rewrite,
        )
        // let empty_cond: Vec<$crate::trs::IsNotZeroCondition> = vec![];
        // $crate::trs::ConditionRewrite::new(
        //     rewrite,
        //     // vec![],
        //     empty_cond
        // )
    }};

    (
        $name:expr;
        $lhs:tt => $rhs:tt
        $(if $cond:expr)+
    )  => {{
        let searcher = $crate::__rewrite2!(@parse $lhs);
        let core_applier = $crate::__rewrite2!(@parse $rhs);
        let applier = $crate::__rewrite2!(@applier core_applier; $($cond,)*);
        // egg::rewrite::new_with_condition(
        //     $name,
        //     ($lhs).to_string(),
        //     ($rhs).to_string(),
        //     // vec![$(stringify!($cond).to_string()),*],
        //     // move |egraph, id, subst| {
        //     //     true $(&& ($cond)(egraph, id, subst))*
        //     // },
        //     searcher,
        //     applier,
        // )
        let rewrite = egg::Rewrite::new(
            $name,
            ($lhs).to_string(),
            ($rhs).to_string(),
            // no conditions given
            // vec![],
            // None::<fn(&mut _, _, _) -> bool>,
            // None::<std::sync::Arc<dyn egg::Condition<_, _>>>,
            // None,
            searcher,
            applier
        ).unwrap();
        $crate::simplify::ConditionRewrite::new(
            rewrite,
            vec![$($cond),*],
        )
        // $crate::Rewrite::new(
        //     $name,
        //     ($lhs).to_string(),
        //     ($rhs).to_string(),
        //     // collect string representations of conditions
        //     vec![$(stringify!($cond).to_string()),*],
        //     // combined condition: call each provided condition and AND the results
        //     // Some(std::sync::Arc::new(move |egraph, id, subst| {
        //     //     true $(&& ($cond)(egraph, id, subst))*
        //     // })),
        //     Some(std::sync::Arc::new($crate::rewrite::FnCondition(move |egraph, id, subst| {
        //         true $(&& ($cond)(egraph, id, subst))*
        //     }))),
        //     searcher,
        //     applier,
        // ).unwrap()
    }};

    (
        $name:expr;
        $lhs:tt <=> $rhs:tt
        $(if $cond:expr)*
    )  => {{
        let name = $name;
        let name2 = String::from(name.clone()) + "-rev";
        vec![
            $crate::rewrite2!(name;  $lhs => $rhs $(if $cond)*),
            $crate::rewrite2!(name2; $rhs => $lhs $(if $cond)*)
        ]
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __rewrite2 {
    (@parse $rhs:literal) => {
        $rhs.parse::<egg::Pattern<_>>().unwrap()
    };
    (@parse $rhs:expr) => { $rhs };
    (@applier $applier:expr;) => { $applier };
    (@applier $applier:expr; $cond:expr, $($conds:expr,)*) => {
        egg::ConditionalApplier {
            // condition: $cond,
            condition: $crate::simplify::ExtendedConditionWrapper($cond),
            applier: $crate::__rewrite2!(@applier $applier; $($conds,)*)
        }
    };
}























#[derive(Clone)]
// pub struct CpKey(pub Id, pub String, pub Vec<String>, pub Option<Arc<dyn Condition<Math, ConstantFold>>>);
// pub struct CpKey(pub Id, pub Rewrite);
pub struct CpKey(pub Id, pub Rc<Rewrite>);

impl PartialEq for CpKey {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1.rewrite.name == other.1.rewrite.name
        // self.0 == other.0 && Rc::ptr_eq(&self.1, &other.1)
    }
}
impl Eq for CpKey {}

impl Hash for CpKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.1.rewrite.name.hash(state);
        // ptr::hash(Rc::as_ptr(&self.1), state);
    }
}






pub trait ExtendedCondition<L,N>
where
    L: Language,
    N: Analysis<L>,
{
    fn as_condition(&self) -> Arc<dyn Condition<L, N>>;

    // handle Condition::vars correctly, or here
    fn vars(&self) -> Vec<Var>;

    // fn apply_subst(&mut self, subst: &HashMap<Var, Var>) -> ();
    // fn with_subst(&self, subst: &HashMap<Var, Var>) -> Self where Self: Sized;
    fn with_subst(&self, subst: &HashMap<Var, Var>) -> Arc<dyn ExtendedCondition<L,N>>;

    fn stringify(&self) -> String;
}

pub struct ExtendedConditionWrapper<T>(pub T);

impl<T, L, N> Condition<L, N> for ExtendedConditionWrapper<T>
where 
    L: Language,
    N: Analysis<L>,
    T: ExtendedCondition<L, N> 
{
    fn vars(&self) -> Vec<Var> {
        <T as ExtendedCondition<L, N>>::vars(&self.0)
    }

    fn check(&self, egraph: &mut egg::EGraph<L, N>, eclass: Id, subst: &Subst) -> bool {
        self.0.as_condition().check(egraph, eclass, subst)
    }
}

#[derive(Clone)]
pub struct ConditionRewrite<L,N> {
    pub rewrite: egg::Rewrite<L,N>,
    pub conditions: Vec<Arc<dyn ExtendedCondition<L,N>>>,
}

impl Hash for ConditionRewrite<Math, ConstantFold> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.rewrite.name.hash(state);
        self.rewrite.lhs.hash(state);
        self.rewrite.rhs.hash(state);
        // // self.conditions.hash(state);
        // for cond in &self.conditions {
        //     cond.stringify().hash(state);
        // }
    }
}

impl Eq for ConditionRewrite<Math, ConstantFold> {}

impl PartialEq for ConditionRewrite<Math, ConstantFold> {
    fn eq(&self, other: &Self) -> bool {
        self.rewrite.name == other.rewrite.name
        && self.rewrite.lhs == other.rewrite.lhs
        && self.rewrite.rhs == other.rewrite.rhs
        // && self.conditions == other.conditions
        && self.conditions.iter().map(|c| c.stringify()).collect::<Vec<_>>() == other.conditions.iter().map(|c| c.stringify()).collect::<Vec<_>>()
    }
}




impl<L,N> Into<egg::Rewrite<L,N>> for ConditionRewrite<L,N>
where
    L: Language,
    N: Analysis<L>,
{
    fn into(self) -> egg::Rewrite<L,N> {
        self.rewrite
    }
}

impl<L,N> ConditionRewrite<L,N> 
where
    L: Language,
    N: Analysis<L>,
{
    pub fn new(
        rewrite: egg::Rewrite<L,N>,
        conditions: Vec<impl ExtendedCondition<L,N> + 'static>,
    ) -> Self {
        let conditions = conditions
                .into_iter()
                .map(|c| 
                    Arc::new(c) as Arc<dyn ExtendedCondition<L,N>>
                    // Arc::new(ExtendedConditionWrapper(c)) as Arc<dyn Condition<L,N>>
                )
                .collect();
        Self {
            rewrite,
            conditions,
        }
    }

    pub fn new_arc(
        rewrite: egg::Rewrite<L,N>,
        conditions: Vec<Arc<dyn ExtendedCondition<L,N>>>,
    ) -> Self {
        let conditions = conditions
                .into_iter()
                .collect();
        Self {
            rewrite,
            conditions,
        }
    }


    pub fn of_rewrite(
        rewrite: egg::Rewrite<L,N>,
    ) -> Self {
        Self {
            rewrite,
            conditions: vec![],
        }
    }
}

#[derive(Debug, Clone)]
pub struct IsNotZeroCondition {
    pub var: Var,
}

impl IsNotZeroCondition {
    pub fn new(var: &str) -> Self {
        Self { var: var.parse().unwrap() }
    }
}

impl ExtendedCondition<Math, ConstantFold> for IsNotZeroCondition {
    fn as_condition(&self) -> Arc<dyn Condition<Math, ConstantFold>> {
        let zero = Math::Constant(0);
        let var = self.var.clone();
        let fun = move |egraph: &mut EGraph, _, subst:&Subst| {
            !egraph[subst[var]].nodes.contains(&zero)
        };
        Arc::new(fun)
    }

    fn vars(&self) -> Vec<Var> {
        vec![self.var.clone()]
    }

    // fn apply_subst(&mut self, subst: &HashMap<Var, Var>) -> () {
    //     if let Some(v) = subst.get(&self.var) {
    //         self.var = v.clone();
    //     }
    // }
    fn with_subst(&self, subst: &HashMap<Var, Var>) -> Arc<dyn ExtendedCondition<Math, ConstantFold>> {
        let mut new_cond = self.clone();
        if let Some(v) = subst.get(&self.var) {
            new_cond.var = v.clone();
        }
        Arc::new(new_cond)
    }

    fn stringify(&self) -> String {
        format!("IsNotZero({})", self.var)
    }
}


#[derive(Debug, Clone)]
pub struct IsConstPosCondition {
    pub var: Var,
}
impl IsConstPosCondition {
    pub fn new(var: &str) -> Self {
        Self { var: var.parse().unwrap() }
    }
}
impl ExtendedCondition<Math, ConstantFold> for IsConstPosCondition {
    fn as_condition(&self) -> Arc<dyn Condition<Math, ConstantFold>> {
        let var = self.var.clone();
        Arc::new(move |egraph: &mut EGraph, _, subst:&Subst| {
            egraph[subst[var]].nodes.iter().any(|n| match n {
                Math::Constant(c) => c > &0,
                _ => return false,
            })
        })
    }
    fn vars(&self) -> Vec<Var> {
        vec![self.var.clone()]
    }
    // fn apply_subst(&mut self, subst: &HashMap<Var, Var>) -> () {
    //     if let Some(v) = subst.get(&self.var) {
    //         self.var = v.clone();
    //     }
    // }
    fn with_subst(&self, subst: &HashMap<Var, Var>) -> Arc<dyn ExtendedCondition<Math, ConstantFold>> {
        let mut new_cond = self.clone();
        if let Some(v) = subst.get(&self.var) {
            new_cond.var = v.clone();
        }
        Arc::new(new_cond)
    }

    fn stringify(&self) -> String {
        format!("IsConstPos({})", self.var)
    }
}
#[derive(Debug, Clone)]
pub struct IsConstNegCondition {
    pub var: Var,
}
impl IsConstNegCondition {
    pub fn new(var: &str) -> Self {
        Self { var: var.parse().unwrap() }
    }
}
impl ExtendedCondition<Math, ConstantFold> for IsConstNegCondition {
    fn as_condition(&self) -> Arc<dyn Condition<Math, ConstantFold>> {
        let var = self.var.clone();
        Arc::new(move |egraph: &mut EGraph, _, subst:&Subst| {
            egraph[subst[var]].nodes.iter().any(|n| match n {
                Math::Constant(c) => c < &0,
                _ => return false,
            })
        })
    }
    fn vars(&self) -> Vec<Var> {
        vec![self.var.clone()]
    }
    // fn apply_subst(&mut self, subst: &HashMap<Var, Var>) -> () {
    //     if let Some(v) = subst.get(&self.var) {
    //         self.var = v.clone();
    //     }
    // }
    fn with_subst(&self, subst: &HashMap<Var, Var>) -> Arc<dyn ExtendedCondition<Math, ConstantFold>> {
        let mut new_cond = self.clone();
        if let Some(v) = subst.get(&self.var) {
            new_cond.var = v.clone();
        }
        Arc::new(new_cond)
    }
    fn stringify(&self) -> String {
        format!("IsConstNeg({})", self.var)
    }
}


#[derive(Debug, Clone)]
pub struct CompareC0C1Condition {
    pub var0: Var,
    pub var1: Var,
    pub comparison: &'static str
}

impl CompareC0C1Condition {
    pub fn new(var0: &str, var1: &str, comparison: &'static str) -> Self {
        Self { 
            var0: var0.parse().unwrap(),
            var1: var1.parse().unwrap(),
            comparison,
        }
    }
}

impl ExtendedCondition<Math, ConstantFold> for CompareC0C1Condition {
    fn as_condition(&self) -> Arc<dyn Condition<Math, ConstantFold>> {
        // Arc::new(crate::trs::compare_c0_c1_fun(self.var0, self.var1, self.comparison))
        let var = self.var0.clone();
        let var1 = self.var1.clone();
        let comp = self.comparison;
        Arc::new(move |egraph: &mut EGraph, _, subst:&Subst| {

            if subst.get(var).is_none() {
                panic!("Variable {:?} (var1: {:?}, comp: {:?}) not found in substitution {:?}", var, var1, comp, subst);
            }
            if subst.get(var1).is_none() {
                panic!("Variable1 {:?} (var: {:?}, comp: {:?}) not found in substitution {:?}", var1, var, comp, subst);
            }

            // Get the eclass of the first constant then match the values of its enodes to check if one of them proves the coming conditions
            egraph[subst[var1]].nodes.iter().any(|n1| match n1 {
                // Get the eclass of the second constant then match it to c1
                Math::Constant(c1) => egraph[subst[var]].nodes.iter().any(|n| match n {
                    // match the comparison then do it
                    Math::Constant(c) => match comp {
                        "<" => c < c1,
                        "<a" => c < &c1.abs(),
                        "<=" => c <= c1,
                        "<=+1" => c <= &(c1 + 1),
                        "<=a" => c <= &c1.abs() && c1 != &0,
                        "<=-a" => c <= &(-c1.abs()) && c1 != &0,
                        "<=-a+1" => c <= &(1 - c1.abs()) && c != &0,
                        ">" => c > c1,
                        // ">a" => c > &c1.abs(),
                        ">=" => c >= c1,
                        ">=a" => c >= &(c1.abs()) && c1 != &0,
                        ">=a-1" => c >= &(c1.abs() - 1) && c1 != &0,
                        "!=" => c != c1,
                        "%0" => (*c1 != 0) && (c % c1 == 0),
                        "!%0" => (*c1 != 0) && (c % c1 != 0),
                        "%0<" => (*c1 > 0) && (c % c1 == 0),
                        "%0<0" => (*c1 > 0) && (c % c1 == 0) && (c != &0),
                        "%0>" => (*c1 < 0) && (c % c1 == 0),
                        _ => false,
                    },
                    _ => return false,
                }),
                _ => return false,
            })
        })
    }

    fn vars(&self) -> Vec<Var> {
        vec![self.var0.clone(), self.var1.clone()]
    }

    // fn apply_subst(&mut self, subst: &HashMap<Var, Var>) -> () {
    //     if let Some(v) = subst.get(&self.var0) {
    //         self.var0 = v.clone();
    //     }
    //     if let Some(v) = subst.get(&self.var1) {
    //         self.var1 = v.clone();
    //     }
    // }

    fn with_subst(&self, subst: &HashMap<Var, Var>) -> Arc<dyn ExtendedCondition<Math, ConstantFold>> {
        let mut new_cond = self.clone();
        if let Some(v) = subst.get(&self.var0) {
            new_cond.var0 = v.clone();
        }
        if let Some(v) = subst.get(&self.var1) {
            new_cond.var1 = v.clone();
        }
        Arc::new(new_cond)
    }

    fn stringify(&self) -> String {
        format!("CompareC0C1({}, {}, {})", self.var0, self.var1, self.comparison)
    }
}


#[derive(Debug, Clone)]
pub struct CompareCondition {
    pub vars: Vec<Var>,
    // pub evaluation: impl Fn(Vec<i64>) -> bool + 'static,
    // pub evaluation: fn(Vec<i64>) -> bool,
    pub evaluation: fn(BTreeMap<String, i64>) -> bool,
    // map new substed vars back to original
    pub var_subst: BTreeMap<Var, Var>,
}

impl CompareCondition {
    pub fn new(vars: Vec<&str>, evaluation: fn(BTreeMap<String, i64>) -> bool) -> Self {
        let vars : Vec<Var> = vars.into_iter().map(|v| v.parse().unwrap()).collect();
        Self {
            vars: vars.clone(),
            evaluation,
            var_subst: // vars -> vars
                vars.iter()
                .map(|v| {
                    (v.clone(), v.clone())
                })
                .collect(),
        }
    }
}



















fn canonical_name_rewrite(rewrite: Rewrite) -> Rewrite {

    // collect all variables from lhs, rhs, and conditions
    // note: this should be equivalent to vars lhs
    let lhs_vars = vars(&rewrite.rewrite.lhs);
    let rhs_vars = vars(&rewrite.rewrite.rhs);
    let condition_vars = rewrite.conditions.iter()
        .flat_map(|c| 
            c.vars().iter().map(|v| v.to_string()).collect::<Vec<_>>()
        )
        .collect::<Vec<_>>();
    // assert that rhs and condition to now have new variables that are not in lhs
    if !rhs_vars.iter().all(|v| lhs_vars.contains(v)) {
        panic!("RHS has variables that are not in LHS: {:?}", rhs_vars.iter().filter(|v| !lhs_vars.contains(v)).collect::<Vec<_>>());
    }
    if !condition_vars.iter().all(|v| lhs_vars.contains(v)) {
        panic!("Conditions have variables that are not in LHS: {:?}", condition_vars.iter().filter(|v| !lhs_vars.contains(v)).collect::<Vec<_>>());
    }

    let mut all_vars = 
        lhs_vars.into_iter()
        .chain(rhs_vars.into_iter())
        .chain(condition_vars.into_iter())
        .collect::<Vec<_>>();

    all_vars.sort();
    all_vars.dedup();

    let subst_map : HashMap<String, String> = all_vars.iter().enumerate()
        .map(|(i, v)| {
            (v.clone(), format!("?v{}", i))
        }).collect();
    let var_subst_map : HashMap<Var, Var> = subst_map.iter()
        .map(|(s, t)| {
            let old_var = s.parse().unwrap();
            let new_var = t.parse().unwrap();
            (old_var, new_var)
        }).collect();
    let subst_set : SubstitutionSet = subst_map.iter()
        .map(|(s, t)| {
            let old_var = s.clone();
            let new_term = parse_term(t);
            (old_var, new_term)
        }).collect();

    let new_lhs = subst(&subst_set, &rewrite.rewrite.lhs);
    let new_rhs = subst(&subst_set, &rewrite.rewrite.rhs);

    let new_conditions = rewrite.conditions.
        iter()
        .map(|c| c.with_subst(&var_subst_map))
        .collect::<Vec<_>>();

    let new_lhs_pattern = Pattern::from_str(&new_lhs.to_string()).unwrap();
    let new_rhs_pattern = Pattern::from_str(&new_rhs.to_string()).unwrap();

    // println!("Canonicalizing rewrite: {}", rewrite.rewrite.name);
    // println!("  Old LHS: {}", rewrite.rewrite.lhs);
    // println!("  Old RHS: {}", rewrite.rewrite.rhs);
    // println!("  New LHS: {}", new_lhs);
    // println!("  New RHS: {}", new_rhs);
    // println!("  Old Conditions: {}", rewrite.conditions.iter().map(|c| c.stringify()).collect::<Vec<_>>().join(", "));
    // println!("  New Conditions: {}", new_conditions.iter().map(|c| c.stringify()).collect::<Vec<_>>().join(", "));
    // // patterns
    // println!("  Old LHS Pattern: {}", rewrite.rewrite.lhs);
    // println!("  Old RHS Pattern: {}", rewrite.rewrite.rhs);
    // println!("  New LHS Pattern: {}", new_lhs_pattern);
    // println!("  New RHS Pattern: {}", new_rhs_pattern);
    // // panic!("Stop after canonicalization");


    let new_applier = ConditionalApplier {
        condition: all_conditions_extended(new_conditions.clone()),
        applier: new_rhs_pattern.clone()
    };

    ConditionRewrite::new_arc(
        egg::Rewrite::new(
            rewrite.rewrite.name,
            // lhs: new_lhs,
            // rhs: new_rhs,
            new_lhs_pattern.to_string(),
            new_rhs_pattern.to_string(),
            new_lhs_pattern,
            new_applier
        ).unwrap(),
        new_conditions
    )

    // rewrite
    // TODO:
    // let mut new_rewrite = rewrite.clone();
    // new_rewrite.rewrite.name = rewrite.rewrite.name.split("::").last().unwrap().to_string();
    // new_rewrite
}


pub fn simplify_expression(expression: &ExpressionStruct, loggers: &Loggers, params: &Args) -> ResultStructure {

    // println!("Starting Expression: {}", expression.index);
    let start_expression = &expression.expression;
    // let report = false;


    // Parse the start expression and the goals.
    let start: RecExpr<Math> = start_expression.parse().unwrap();
    let end_1: Pattern<Math> = "1".parse().unwrap();
    let end_0: Pattern<Math> = "0".parse().unwrap();

    // Put the goals we want to check in an array.
    let goals = [end_0.clone(), end_1.clone()];
    let mut result = false;
    let mut proved_goal_index = 0;
    let mut id;
    let best_expr;
    let mut total_time: f64 = 0.0;
    // let nbr_passes = (params.2 as f64) / threshold;
    let threshold = params.total_time as f64 / (params.iterations as f64);

    info!(loggers.logger, "Starting expression {}: {}", expression.index, start_expression);

    // if report {
    //     println!(
    //         "\n====================================\nProving Expression:\n {}\n",
    //         start_expression
    //     )
    // }

    let mut i = 0;
    let mut expr = start;

    //Initialize the runner with the limits and the initial expression.
    // let mut runner = Runner::default()
    //     .with_iter_limit(params.0)
    //     .with_node_limit(params.1)
    //     .with_time_limit(Duration::from_secs_f64(threshold))
    //     .with_expr(&expr);
    let mut runner;
    // Get the Id of the root eclass containing the initial expression.
    // id = runner.egraph.find(*runner.roots.last().unwrap());


    let rules = crate::rules::rules();
    let mut cp_rules = Vec::<Rewrite>::new();
    let mut critical_pairs_set = HashSet::<(String,String)>::new();
    // let mut critical_pairs_set = HashSet::<(Rewrite,Rewrite)>::new();
    // let mut critical_pairs = HashSet::<(String,(Id,String, Vec<String>, ),(Id,String, Vec<String>))>::new();
    let mut critical_pairs = HashSet::<(String,CpKey,CpKey)>::new();
        // (Id,String, Vec<String>, Option<Arc<dyn Condition<Math, ConstantFold>>>)
        // (Id,String, Vec<String>, Option<Arc<dyn Condition<Math, ConstantFold>>>))>::new();
    let mut rule_name_counter = 0;

    // let keep_cp_rules = 100;
    // let keep_cp_rules = 1000;
    // let keep_cp_rules = 0;
    // let keep_cp_rules = 75;
    // let keep_cp_rules = 5;
    // let keep_cp_rules = 100;
    // let keep_cp_rules = 50;
    let keep_cp_rules = params.cp_count;

    // let rules_for_cp_count = 10;
    let rules_for_cp_count = params.cp_retain;
    // let rules_for_cp_count = 0;

    // let applied_rule_file = std::fs::OpenOptions::new()
    //     .create(true)
    //     .append(true)
    //     .open("tmp/applied_rules.txt")
    //     .unwrap();
    // let mut applied_rule_writer = BufWriter::new(applied_rule_file);
    // {
    //     writeln!(applied_rule_writer, "ID {}:", expression.index).unwrap();
    //     writeln!(applied_rule_writer, "Expression: {}", start_expression).unwrap();
    // }
    info!(loggers.applied_rules, "ID {}:", expression.index);
    info!(loggers.applied_rules, "Expression: {}", start_expression);



    // Run ES on each extracted expression until we reach a limit or we prove the expression.
    loop {
        info!(loggers.logger, "  Iteration {}", i);
        let runner_builder = Runner::default()
            .with_iter_limit(params.egraph_iterations)
            .with_node_limit(params.nodes)
            .with_time_limit(Duration::from_secs_f64(threshold))
            .with_expr(&expr);

        cp_rules
            .sort_by_key(|cr| {
                let r = &cr.rewrite;
                // let lhs_size = term_size(&r.lhs);
                let rhs_size = term_size(&r.rhs);
                // lhs_size + rhs_size
                rhs_size
            });

        cp_rules = cp_rules.into_iter()
            .map(canonical_name_rewrite)
            .collect::<HashSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();

        // take 1000 smallest according to size lhs+rhs
        let picked_cp_rules = cp_rules
            .iter()
            .take(keep_cp_rules)
            .cloned()
            .collect::<Vec<_>>();

            // if picked_cp_rules.len() > 0 {
            //     panic!("Stop after canonicalization");
            // }

        // println!("Used CP rules ({}): ", picked_cp_rules.len());
        // for r in picked_cp_rules.iter() {
        //     println!("  {}: {} => {} (with conditions: {})", r.rewrite.name, r.rewrite.lhs, r.rewrite.rhs, r.conditions.iter().map(|c| c.stringify()).collect::<Vec<_>>().join(", "));
        // }

        let all_rules = rules.iter().chain(picked_cp_rules.iter()).collect::<Vec<_>>();

        // println!("VVV: Running EGraph");
        // io::stdout().flush().unwrap();
        info!(loggers.logger, "    Egraph");
        measure_block!("egraph", {
        runner = 
        // if use_iteration_check {
            runner_builder.run_check_iteration(all_rules.iter().map(|r| &r.rewrite), &goals);
        // } else {
        //     runner_builder.run(all_rules.iter().map(|r| &r.rewrite))
        // };
        }); // measure
        //Check if the expression is proved.
        id = runner.egraph.find(*runner.roots.last().unwrap());
        for (goal_index, goal) in goals.iter().enumerate() {
            let boolean = (goal.search_eclass(&runner.egraph, id)).is_none();
            if !boolean {
                result = true;
                proved_goal_index = goal_index;
                break;
            }
        }
        // println!("VVV: Finished EGraph");
        // io::stdout().flush().unwrap();

        //If we saturate then the expression is unprovable using our ruleset.
        let saturated = match &runner.stop_reason.as_ref().unwrap() {
            StopReason::Saturated => true,
            _ => false,
        };
        let exec_time: f64 = runner.iterations.iter().map(|i| i.total_time).sum();
        total_time += exec_time;
        //Exit the loop if we saturated or reached the limits.
        if saturated || i >= params.iterations || result {
            break;
        }
        i += 1;

        //Extract the best expression from the egraph.
        let mut extractor;
        let extraction_time;
        info!(loggers.logger, "    Extraction");
        measure_block!("extraction", {
        extractor = Extractor::new(&((&runner).egraph), AstDepth);

        //Calculate the extraction time.
        let now = Instant::now();
        let (_, best_exprr) = extractor.find_best(id);
        extraction_time = now.elapsed().as_secs_f64();
        expr = best_exprr;
        total_time += extraction_time;
        }); // measure
        // if report {
        //     println!(
        //         "Starting pass {} with Expr: {} in {}",
        //         i,
        //         format!("{}", expr).bright_green().bold(),
        //         format!("{}", extraction_time).bright_green().bold()
        //     );
        // }




        let rules_for_cp = 
            rules.iter().chain(
                cp_rules
                .iter()
                .take(rules_for_cp_count)
            )
            .cloned()
            .collect::<Vec<_>>();

        info!(loggers.logger, "    Collect Parents");
        // println!("VVV: Collecting RuleApp");
        // io::stdout().flush().unwrap();

        let max_id_usize = runner.egraph.classes()
            .map(|c| usize::from(c.id))
            .max()
            .unwrap_or(0);

        // 2. Use a flat vector instead of HashMap for parents
        let mut parents: Vec<Vec<Id>> = vec![Vec::new(); max_id_usize + 1];

        measure_block!("collect parents", {
            for eclass in runner.egraph.classes() {
                for node in &eclass.nodes {
                    node.for_each(|child| {
                        parents[usize::from(child)].push(eclass.id);
                    });
                }
            }
            
            // Deduplicate parents to avoid redundant propagation
            for p_list in &mut parents {
                p_list.sort_unstable();
                p_list.dedup();
            }
        });

            // parents: for each eclass a list of classes that reference it
        //     let mut parents = std::collections::HashMap::<Id, Vec<Id>>::new();
        // measure_block!("collect parents", {
        //     for eclass in runner.egraph.classes().map(|c| c) {
        //         for node in &eclass.nodes {
        //             node.for_each(|child| {
        //                 parents
        //                     .entry(child)
        //                     .or_insert_with(Vec::new)
        //                     .push(eclass.id);
        //             });
        //         }
        //     }
        // }); // measure


        // println!("VVV: Propagate Parents1");
        // io::stdout().flush().unwrap();


// let mut sub_applicable = std::collections::HashMap::<Id, std::collections::HashSet<CpKey>>::new();

// measure_block!("rule parents", {
//     for r in rules_for_cp.into_iter() {
//         let matches = r.rewrite.search(&runner.egraph);
        
//         let mut worklist: Vec<(Id, Id)> = matches.iter()
//             .map(|m| (m.eclass, m.eclass)) // (current, source)
//             .collect();
            
//         while let Some((current, source)) = worklist.pop() {
            
//             // TODO: no clone (use id/name/rc<>)
//             let new_key = CpKey(source, r.clone()); 
            
//             let entry = sub_applicable
//                 .entry(current)
//                 .or_insert_with(std::collections::HashSet::new);
                
//             if entry.insert(new_key) {
//                 if let Some(ps) = parents.get(&current) {
//                     for p in ps {
//                         worklist.push((*p, source));
//                     }
//                 }
//             }
//         }
//     }
// });

        info!(loggers.logger, "    Rule Parents");
let mut sub_applicable: Vec<FxHashSet<CpKey>> = vec![FxHashSet::default(); max_id_usize + 1];

measure_block!("rule parents", {
    for r in rules_for_cp.into_iter() {
        let rc_rule = Rc::new(r);
        let matches = rc_rule.rewrite.search(&runner.egraph);
        
        let mut worklist: Vec<(Id, Id)> = matches.iter()
            .map(|m| (m.eclass, m.eclass)) // (current, source)
            .collect();
            
        while let Some((current, source)) = worklist.pop() {
            
            // 2. Clone the Rc, NOT the rule! (This is just an 8-byte pointer copy + counter increment)
            let new_key = CpKey(source, Rc::clone(&rc_rule)); 
            
            // O(1) array access + fast FxHashSet insert with pointer hashing
            let is_new = sub_applicable[usize::from(current)].insert(new_key);
                
            if is_new {
                // O(1) array access to the parents array we built earlier
                let ps = &parents[usize::from(current)];
                for &p in ps {
                    worklist.push((p, source));
                }
            }
        }
    }
});


            // propagate upwards, eclass -> application point, rule, and condition
            // let mut sub_applicable = std::collections::HashMap::<Id, HashSet<(Id,String, Vec<String>, Option<Arc<dyn Condition<Math, ConstantFold>>>)>>::new();
            // let mut sub_applicable = std::collections::HashMap::<Id, HashSet<CpKey>>::new();
        //     let mut sub_applicable = std::collections::HashMap::<Id, Vec<CpKey>>::new();
        // measure_block!("rule parents", {
        //     for r in rules_for_cp.into_iter() {
        //     // for r in rules.clone().into_iter() {
        //         // if !r.cond.is_empty() {
        //         //     continue;
        //         // }
        //         let matches = r.rewrite.search(&runner.egraph);
        //         // eclasses where the rule applies
        //         let mut worklist = matches.iter()
        //             .map(|m| m.eclass)
        //             .map(|id| (id, id)) // (current, source)
        //             .collect::<HashSet<_>>();
        //         while !worklist.is_empty() {
        //             let (current, source) = worklist.iter().next().unwrap().clone();
        //             worklist.remove(&(current, source));
        //             let entry = sub_applicable
        //                 .entry(current)
        //                 // .or_insert_with(HashSet::new);
        //                 .or_insert_with(Vec::new);
        //             let new_key = CpKey(source, r.clone());
        //             let fresh = !entry.iter().any(|c| c == &new_key);
        //             if fresh {
        //                 entry.push(new_key);
        //                 if let Some(ps) = parents.get(&current) {
        //                     for p in ps {
        //                         worklist.insert((*p, source));
        //                     }
        //                 }
        //             }
        //             // if entry.insert(CpKey(source, r.clone())) {
        //             //     // only continue when freshly inserted => terminate at the latest after every eclass has been visited once
        //             //     if let Some(ps) = parents.get(&current) {
        //             //         for p in ps {
        //             //             worklist.insert((*p, source));
        //             //         }
        //             //     }
        //             // }
        //         }
        //     }
        // }); // measure

        // println!("VVV: Write applicable rules to file");
        // io::stdout().flush().unwrap();
        //     writeln!(applied_rule_writer, " Iteration {}:", i).unwrap();
        info!(loggers.applied_rules, " Iteration {}:", i);
        // for (eclass, apps) in sub_applicable.iter() {
        for (eclass, apps) in sub_applicable.iter().enumerate() {
            for CpKey(src, rule) in apps.iter() {
                if usize::from(*src) != eclass {
                    continue;
                }
                let rule_string =
                    rule.rewrite.name.clone() + ": " + &rule.rewrite.lhs.to_string() + " => " + &rule.rewrite.rhs.to_string() + " with " + &format!("{:?}", rule.conditions.iter().map(|c| c.stringify()).collect::<Vec<_>>());
                // writeln!(applied_rule_writer, "  EClass {}: applied rule {}", eclass, rule_string).unwrap();
                info!(loggers.applied_rules, "  EClass {}: applied rule {}", eclass, rule_string);
            }
        }


        // println!("VVV: Propagate Parents2");
        // io::stdout().flush().unwrap();
        info!(loggers.logger, "    Find CP candidates");

            // only propagate up to either other node => intersection only at one of the rules
            // at class c, get all pairs and take these that have one component be c
            // find overlaps
measure_block!("find cp candidate", {
    // sub applicate: e class -> list of all rules applicable together with origin
    // for (eclass, apps) in sub_applicable.iter() {
    for (eclass, apps) in sub_applicable.iter().enumerate() {
        let mut local_apps = Vec::new();
        let mut inherited_apps = Vec::new();
        
        for app in apps {
            if usize::from(app.0) == eclass { // app.0 is the `src` Id
                local_apps.push(app);
            } else {
                inherited_apps.push(app);
            }
        }

        let mut process_pair = |app_i: &CpKey, app_j: &CpKey| {
            let CpKey(src_i, rule_i) = app_i;
            let CpKey(src_j, rule_j) = app_j;
            
            let name_i = rule_i.rewrite.name();
            let name_j = rule_j.rewrite.name();
            
            let pair = if name_i < name_j {
                // (name_i, name_j) 
                (name_i.to_string(), name_j.to_string())
            } else {
                // (name_j, name_i)
                (name_j.to_string(), name_i.to_string())
            };
            
            if critical_pairs_set.insert(pair) {
                let cp_count = critical_pairs_set.len();
                // TODO: usize not string for name
                // TODO: use Rc for key to avoid clone
                critical_pairs.insert((
                    // cp_count, 
                    cp_count.to_string(),
                    CpKey(*src_i, rule_i.clone()), 
                    CpKey(*src_j, rule_j.clone())
                ));
            }
        };

        for i in 0..local_apps.len() {
            for j in (i + 1)..local_apps.len() {
                process_pair(local_apps[i], local_apps[j]);
            }
        }

        for local in &local_apps {
            for inherited in &inherited_apps {
                process_pair(local, inherited);
            }
        }
    }
});

        // measure_block!("find cp candidate", {
        //     for (eclass, apps) in sub_applicable.iter() {
        //         // let apps_vec = apps.iter().collect::<Vec<_>>();
        //         let apps = apps.iter().collect::<Vec<_>>();
        //         for i in 0..apps.len() {
        //             for j in (i + 1)..apps.len() {
        //         // for i in 0..apps_vec.len() {
        //         //     for j in (i + 1)..apps_vec.len() {
        //                 let CpKey(src_i, rule_i) = &apps[i];
        //                 let CpKey(src_j, rule_j) = &apps[j];
        //                 // let CpKey(src_i, rule_i) = apps_vec[i];
        //                 // let CpKey(src_j, rule_j) = apps_vec[j];
        //                 if src_i != eclass && src_j != eclass {
        //                     continue;
        //                 }
        //                 let name_i = rule_i.rewrite.name();
        //                 let name_j = rule_j.rewrite.name();
        //                 // sorted tuple in critical pairs
        //                 let pair = if name_i < name_j {
        //                     (name_i.to_string(), name_j.to_string())
        //                 } else {
        //                     (name_j.to_string(), name_i.to_string())
        //                 };
        //                 if critical_pairs_set.insert(pair) {
        //                     let cp_count = critical_pairs_set.len();
        //                     critical_pairs.insert((cp_count.to_string(), CpKey(*src_i, rule_i.clone()), CpKey(*src_j, rule_j.clone())));
        //                     // println!(
        //                     //     "Overlap found in eclass {}: rules '{}' and '{}' (from eclasses {} and {})",
        //                     //     eclass, rule_i, rule_j, src_i, src_j
        //                     // );
        //                 }
        //                 // println!(
        //                 //     "Overlap found in eclass {}: rules '{}' and '{}' (from eclasses {} and {})",
        //                 //     eclass, rule_i, rule_j, src_i, src_j
        //                 // );
        //             }
        //         }
        //     }
        // }); // measure


        // println!("VVV: Compute CP");
        // io::stdout().flush().unwrap();
        info!(loggers.logger, "    Compute CP");

            // TODO: only critical pair overlap at correct positions not all
            // TODO: only critical pair that were used in e-graph (at node) (custom applier)
        measure_block!("compute cp", {
            for (_cp_name, CpKey(_src1, rule1), CpKey(_src2, rule2)) in critical_pairs.iter() {
                // let rule1 = rules.iter().find(|r| r.rewrite.name() == *r1).unwrap();
                // let rule2 = rules.iter().find(|r| r.rewrite.name() == *r2).unwrap();
                let r1 = (&rule1.rewrite.lhs,&rule1.rewrite.rhs);
                let r2 = (&rule2.rewrite.lhs,&rule2.rewrite.rhs);
                // TODO: subst of critical_pair_parts ignored => variable condition might become subterm condition
                let cps = all_critical_pair_ref(r1, r2);
                for (l, r, unifier, right_subst) in cps.iter() {

                     
                    let var_l = vars(l);
                    let var_r = vars(r);
                    fn is_var(t: &Term) -> bool {
                        matches!(t, Term::Var(_))
                    }
                    let cp_name_lr = format!("cp_{}_lr", rule_name_counter);
                    let cp_name_rl = format!("cp_{}_rl", rule_name_counter);
                    rule_name_counter += 1;

                    let rename_subst_map: HashMap<Var, Var> = right_subst.iter().map(|(k,v)| {
                        let var1 = k.parse().unwrap();
                        let var2 = v.parse().unwrap();
                        (var1, var2)
                    }).collect();
                    let unifier_var_subst: HashMap<String, String> = unifier.iter().filter_map(|(k,v)| {
                        if let Term::Var(var) = v {
                            Some((k.clone(), var.to_string()))
                        } else {
                            None
                        }
                    }).collect();
                    let unifier_subst_map: HashMap<Var, Var> = unifier_var_subst.iter().map(|(k,v)| {
                        let var1 = k.parse().unwrap();
                        let var2 = v.parse().unwrap();
                        (var1, var2)
                    }).collect();
                    // let total_subst_map: HashMap<Var, Var> = rename_subst_map.iter().chain(unifier_subst_map.iter()).map(|(k,v)| (k.clone(), v.clone())).collect();
                    let r2_conds = rule2.conditions.iter().map(|c| {
                        // c.with_subst(&total_subst_map)
                        c.with_subst(&rename_subst_map).with_subst(&unifier_subst_map)
                    }).collect::<Vec<_>>();
                    let r1_conds = rule1.conditions.iter().map(|c| { c.with_subst(&unifier_subst_map) }).collect::<Vec<_>>();
                    let conds = 
                        r1_conds.iter()
                        .chain(r2_conds.iter())
                        .map(|c| { c.clone() })
                        .collect::<Vec<_>>();

                    let condsstr = conds.iter().map(|c| c.stringify()).collect::<Vec<_>>();
                    let condsstr = "conds: ".to_string() + &format!("{:?}", condsstr);

                    let lhs_pattern = Pattern::from_str(&l.to_string()).unwrap();
                    let rhs_pattern = Pattern::from_str(&r.to_string()).unwrap();


                    let condvars = conds.iter().flat_map(|c| 
                        c.vars().iter().map(|v| v.to_string()).collect::<Vec<_>>()
                    ).collect::<HashSet<_>>();

                    // is there a condition variable that does not occur in the rule?
                    if condvars.iter().any(|v| !var_l.contains(v) && !var_r.contains(v)) {
                        info!(loggers.cp_rules, 
                            "Skipping CP rule {}: {} -> {} because condition variable(s) {:?} do not occur in the rule ({})",
                            cp_name_lr,
                            l,
                            r,
                            condvars.iter().filter(|v| !var_l.contains(v) && !var_r.contains(v)).collect::<Vec<_>>(),
                            condsstr
                        );
                        info!(loggers.cp_rules, "  R1: {} -> {} (conds: {:?})\n  R2: {} -> {} (conds: {:?})\n  Rename subst: {:?}\n  Unification: {:?}",
                            rule1.rewrite.lhs,
                            rule1.rewrite.rhs,
                            rule1.conditions.iter().map(|c| c.stringify()).collect::<Vec<_>>(),
                            rule2.rewrite.lhs,
                            rule2.rewrite.rhs,
                            rule2.conditions.iter().map(|c| c.stringify()).collect::<Vec<_>>(),
                            right_subst,
                            unifier.iter().map(|(k,v)| (k.to_string(), v.to_string())).collect::<Vec<_>>()
                        );
                        // panic!();
                        continue;
                    }


                    // if ! conds.is_empty() {
                    //     // for testing
                    //     continue;
                    // }

                    info!(loggers.cp_rules, 
                        // "Adding CP rule: {}: {} -> {} with conditions {:?}\n  (original1: {} -> {}, original2: {} -> {})\n  using CP subst {:?}",
                        "Adding CP rule: {}: {} -> {} with conditions {:?}\n  (original1: {} -> {} with {:?}, original2: {} -> {} with {:?})\n  using Rename subst {:?}\n  using Unifier subst {:?}",
                        cp_name_lr,
                        l,
                        r,
                        condsstr,
                        rule1.rewrite.lhs,
                        rule1.rewrite.rhs,
                        rule1.conditions.iter().map(|c| c.stringify()).collect::<Vec<_>>(),
                        rule2.rewrite.lhs,
                        rule2.rewrite.rhs,
                        rule2.conditions.iter().map(|c| c.stringify()).collect::<Vec<_>>(),
                        right_subst,
                        unifier.iter().map(|(k,v)| (k.to_string(), v.to_string())).collect::<Vec<_>>()
                    );

                    if var_r.iter().all(|v| var_l.contains(v)) && !is_var(l) {
                        // if var_r is subset of var_l 
                        // println!(
                        //     "Adding CP rule: {}: {} -> {} with conditions {:?}\n  (original1: {:?} -> {:?}, original2: {:?} -> {:?})",
                        //     cp_name_lr,
                        //     l,
                        //     r,
                        //     condsstr,
                        //     rule1.rewrite.lhs,
                        //     rule1.rewrite.rhs,
                        //     rule2.rewrite.lhs,
                        //     rule2.rewrite.rhs
                        // );
                        info!(loggers.cp_rules, "Added rule {}: {} -> {}", cp_name_lr, l, r);

                        let cond_applier = 
                            ConditionalApplier {
                                // condition: all_conditions(conds.iter().map(|c| c.as_condition()).collect()),
                                condition: all_conditions_extended(conds.clone()),
                                applier: rhs_pattern.clone(),
                            };

                        // cp_rules.push(rule_of_cp_cond(cp_name_lr.as_str(), l, r, condsstr.clone(), conds.clone()));
                        cp_rules.push(ConditionRewrite::new_arc(
                            egg::Rewrite::new(
                                cp_name_lr.as_str(),
                                lhs_pattern.clone().to_string(),
                                rhs_pattern.clone().to_string(),
                                lhs_pattern.clone(),
                                // rhs_pattern.clone(),
                                cond_applier,
                            ).unwrap(),
                            conds.iter().cloned().collect(),
                        ));
                        // cp_rules.push(rule_of_cp(cp_name_lr.as_str(), l, r));
                    }
                    if var_l.iter().all(|v| var_r.contains(v)) && !is_var(r) {
                        // if var_l is subset of var_r
                        info!(loggers.cp_rules, "Added inverse rule {}: {} -> {}", cp_name_rl, r, l);
                        // println!(
                        //     " Adding CP rule: {}: {} -> {} with conditions {:?}",
                        //     cp_name_rl,
                        //     r,
                        //     l,
                        //     condsstr
                        // );
                        // cp_rules.push(rule_of_cp_cond(cp_name_rl.as_str(), r, l, condsstr, conds));
                        let cond_applier = 
                            ConditionalApplier {
                                // condition: all_conditions(conds.iter().map(|c| c.as_condition()).collect()),
                                condition: all_conditions_extended(conds.clone()),
                                applier: lhs_pattern.clone(),
                            };
                        cp_rules.push(ConditionRewrite::new_arc(
                            egg::Rewrite::new(
                                cp_name_rl.as_str(),
                                rhs_pattern.to_string(),
                                lhs_pattern.to_string(),
                                rhs_pattern,
                                // lhs_pattern,
                                cond_applier,
                            ).unwrap(),
                            conds
                        ));
                        // cp_rules.push(rule_of_cp(cp_name_rl.as_str(), r, l));
                    }
                }
            }















            //         // TODO: not any two if can be unified (same_eq)
            //         //   Critical pair between '((* ?a 1) -> ?a)' and '((* ?a ?b) -> (* ?b ?a))': (* 1 ?a_0) = ?a_0
            //         //   Critical pair between '((* ?a 1) -> ?a)' and '((* ?a ?b) -> (* ?b ?a))': ?a = (* 1 ?a)
            //         // println!(
            //         //     "  Critical pair between '({} -> {})' and '({} -> {})': {} = {}",
            //         //     r1.0,r1.1,
            //         //     r2.0,r2.1,
            //         //     l,
            //         //     r
            //         // );
            //         // add critical pair as rewrite rule
            //         // consider both direction but only if no new variable are introduced

            //         let r_subst = right_subst.iter().cloned().chain(
            //             unifier.iter().filter_map(|(k,v)| {
            //                 if let Term::Var(var) = v {
            //                     // if k is rhs of r_subst_org use lhs instead
            //                     // let k_prime = r_subst_org.iter().find_map(|(k2,v2)| {
            //                     //     if v2 == k {
            //                     //         Some(k2)
            //                     //     } else {
            //                     //         None
            //                     //     }
            //                     // }).unwrap_or(k);
            //                     let k_prime = k;
            //                     Some((k_prime.clone(), var.to_string()))
            //                 } else {
            //                     None
            //                 }
            //             })
            //             // r_subst_org.iter()
            //         ).collect::<Vec<_>>();


            //         let var_l = vars(l);
            //         let var_r = vars(r);
            //         fn is_var(t: &Term) -> bool {
            //             matches!(t, Term::Var(_))
            //         }
            //         let cp_name_lr = format!("cp_{}_lr", rule_name_counter);
            //         let cp_name_rl = format!("cp_{}_rl", rule_name_counter);
            //         rule_name_counter += 1;
            //         // let condsstr = cond1.iter().chain(cond2.iter()).cloned().collect::<Vec<_>>();
            //         // if !condsstr.is_empty() {
            //         //     panic!("Conditional critical pairs not supported yet, got conditions: {:?}", condsstr);
            //         // }
            //         // let conds = if condsstr.is_empty() { None } else { Some(Arc::new(CombinedCondition(conds1, conds2))) };

            //         // let conds = 
            //         //     if let Some(c1) = conds1 {
            //         //         if let Some(c2) = conds2 {
            //         //             Some(Arc::new(CombinedCondition(c1.clone(), c2.clone())) as Arc<dyn Condition<Math, ConstantFold>>)
            //         //         } else {
            //         //             Some(c1.clone())
            //         //         }
            //         //     } else {
            //         //         conds2.clone()
            //         //     };

            //             // TODO: print debug rules

            //         let r_subst_map: HashMap<Var, Var> = r_subst.iter().map(|(k,v)| {
            //             let var1 = k.parse().unwrap();
            //             let var2 = v.parse().unwrap();
            //             (var1, var2)
            //         }).collect();
            //         let r2_conds = rule2.conditions.iter().map(|c| {
            //             // let mut cnew = (*c).clone();
            //             // apply substitution from critical pair unification
            //             // cnew.apply_subst(&r_subst_map);
            //             // cnew
            //             c.with_subst(&r_subst_map)
            //         }).collect::<Vec<_>>();
            //         let r1_conds = rule1.conditions.iter().map(|c| { c.with_subst(&r_subst_map) }).collect::<Vec<_>>();
            //         let conds = 
            //             // rule1.conditions.iter()
            //             r1_conds.iter()
            //             // .chain(rule2.conditions.iter())
            //             .chain(r2_conds.iter())
            //             .map(|c| {
            //                 // let mut cnew = (*c).clone();
            //                 // apply substitution from critical pair unification
            //                 // let subst_cp = unify_terms(l, r).unwrap();
            //                 // cnew.apply_subst(&subst_cp);
            //                 c.clone()
            //             })
            //             .collect::<Vec<_>>();
            //         let condsstr = conds.iter().map(|c| c.stringify()).collect::<Vec<_>>();
            //         let condsstr = "conds: ".to_string() + &format!("{:?}", condsstr);

            //         let lhs_pattern = Pattern::from_str(&l.to_string()).unwrap();
            //         let rhs_pattern = Pattern::from_str(&r.to_string()).unwrap();


            //         let condvars = conds.iter().flat_map(|c| 
            //             c.vars().iter().map(|v| v.to_string()).collect::<Vec<_>>()
            //         ).collect::<HashSet<_>>();

            //         // is there a condition variable that does not occur in the rule?
            //         if condvars.iter().any(|v| !var_l.contains(v) && !var_r.contains(v)) {
            //             println!(
            //                 "Skipping CP rule {}: {} -> {} because condition variable(s) {:?} do not occur in the rule ({})",
            //                 cp_name_lr,
            //                 l,
            //                 r,
            //                 condvars.iter().filter(|v| !var_l.contains(v) && !var_r.contains(v)).collect::<Vec<_>>(),
            //                 condsstr
            //             );
            //             println!(
            //                 "  R1: {} -> {} (conds: {:?})\n  R2: {} -> {} (conds: {:?})\n  Rename subst: {:?}\n  Unification: {:?}",
            //                 rule1.rewrite.lhs,
            //                 rule1.rewrite.rhs,
            //                 rule1.conditions.iter().map(|c| c.stringify()).collect::<Vec<_>>(),
            //                 rule2.rewrite.lhs,
            //                 rule2.rewrite.rhs,
            //                 rule2.conditions.iter().map(|c| c.stringify()).collect::<Vec<_>>(),
            //                 right_subst,
            //                 unifier.iter().map(|(k,v)| (k.to_string(), v.to_string())).collect::<Vec<_>>()
            //             );
            //             // panic!();
            //             continue;
            //         }


            //         // if ! conds.is_empty() {
            //         //     // for testing
            //         //     continue;
            //         // }

            //         println!(
            //             "Adding CP rule: {}: {} -> {} with conditions {:?}\n  (original1: {} -> {}, original2: {} -> {})\n  using CP subst {:?}",
            //             cp_name_lr,
            //             l,
            //             r,
            //             condsstr,
            //             rule1.rewrite.lhs,
            //             rule1.rewrite.rhs,
            //             rule2.rewrite.lhs,
            //             rule2.rewrite.rhs,
            //             r_subst    
            //         );

            //         if var_r.iter().all(|v| var_l.contains(v)) && !is_var(l) {
            //             // if var_r is subset of var_l 
            //             // println!(
            //             //     "Adding CP rule: {}: {} -> {} with conditions {:?}\n  (original1: {:?} -> {:?}, original2: {:?} -> {:?})",
            //             //     cp_name_lr,
            //             //     l,
            //             //     r,
            //             //     condsstr,
            //             //     rule1.rewrite.lhs,
            //             //     rule1.rewrite.rhs,
            //             //     rule2.rewrite.lhs,
            //             //     rule2.rewrite.rhs
            //             // );
            //             println!("Added rule {}: {} -> {}", cp_name_lr, l, r);

            //             let cond_applier = 
            //                 ConditionalApplier {
            //                     // condition: all_conditions(conds.iter().map(|c| c.as_condition()).collect()),
            //                     condition: all_conditions_extended(conds.clone()),
            //                     applier: rhs_pattern.clone(),
            //                 };

            //             // cp_rules.push(rule_of_cp_cond(cp_name_lr.as_str(), l, r, condsstr.clone(), conds.clone()));
            //             cp_rules.push(ConditionRewrite::new_arc(
            //                 egg::Rewrite::new(
            //                     cp_name_lr.as_str(),
            //                     lhs_pattern.clone().to_string(),
            //                     rhs_pattern.clone().to_string(),
            //                     lhs_pattern.clone(),
            //                     // rhs_pattern.clone(),
            //                     cond_applier,
            //                 ).unwrap(),
            //                 conds.iter().cloned().collect(),
            //             ));
            //             // cp_rules.push(rule_of_cp(cp_name_lr.as_str(), l, r));
            //         }
            //         if var_l.iter().all(|v| var_r.contains(v)) && !is_var(r) {
            //             // if var_l is subset of var_r
            //             println!("Added inverse rule {}: {} -> {}", cp_name_rl, r, l);
            //             // println!(
            //             //     " Adding CP rule: {}: {} -> {} with conditions {:?}",
            //             //     cp_name_rl,
            //             //     r,
            //             //     l,
            //             //     condsstr
            //             // );
            //             // cp_rules.push(rule_of_cp_cond(cp_name_rl.as_str(), r, l, condsstr, conds));
            //             let cond_applier = 
            //                 ConditionalApplier {
            //                     // condition: all_conditions(conds.iter().map(|c| c.as_condition()).collect()),
            //                     condition: all_conditions_extended(conds.clone()),
            //                     applier: lhs_pattern.clone(),
            //                 };
            //             cp_rules.push(ConditionRewrite::new_arc(
            //                 egg::Rewrite::new(
            //                     cp_name_rl.as_str(),
            //                     rhs_pattern.to_string(),
            //                     lhs_pattern.to_string(),
            //                     rhs_pattern,
            //                     // lhs_pattern,
            //                     cond_applier,
            //                 ).unwrap(),
            //                 conds
            //             ));
            //             // cp_rules.push(rule_of_cp(cp_name_rl.as_str(), r, l));
            //         }
            //     }
            // }
        }); // measure











    }

    if result {
        // if report {
            info!(loggers.logger,
                "{}\n{:?}",
                "Proved goal:".bright_green().bold(),
                goals[proved_goal_index].to_string()
            );
        // }
        best_expr = Some(goals[proved_goal_index].to_string());
    } else {
        // If we didn't prove anything, then we return the best expression.
        let mut extractor = Extractor::new(&runner.egraph, AstDepth);
        let now = Instant::now();
        let (_, best_exprr) = extractor.find_best(id);
        let extraction_time = now.elapsed().as_secs_f32();

        best_expr = Some(best_exprr.to_string());
        // if report {
            info!(loggers.logger, "{}\n", "Could not prove any goal:".bright_red().bold(),);
            info!(loggers.logger,
                "Best Expr: {}",
                format!("{}", best_exprr).bright_green().bold()
            );
            info!(loggers.logger,
                "{} {}",
                "Extracting Best Expression took:".bright_red(),
                extraction_time.to_string().bright_green()
            );
        // }
    }
    // if report {
    //     runner.print_report();
    // }

    let stop_reason = match runner.stop_reason.unwrap() {
        StopReason::Saturated => "Saturation".to_string(),
        StopReason::IterationLimit(iter) => format!("Iterations: {}", iter),
        StopReason::NodeLimit(nodes) => format!("Node Limit: {}", nodes),
        StopReason::TimeLimit(time) => format!("Time Limit : {}", time),
        StopReason::Other(reason) => reason,
    };

    // export cp_rules to tmp/cp_rules.txt (append if already exists)
    {
        let picked_cp_rules = cp_rules
            .iter()
            .take(keep_cp_rules)
            .map(|r| 
                r.rewrite.name().to_string()+": "+&r.rewrite.lhs.to_string()+" => "+&r.rewrite.rhs.to_string() + " with " + &format!("{:?}", r.conditions.iter().map(|c| c.stringify()).collect::<Vec<_>>())
            )
            .collect::<Vec<_>>()
            .join("\n");

        // let file = std::fs::OpenOptions::new()
        //     .create(true)
        //     .append(true)
        //     .open("tmp/cp_rules.txt")
        //     .unwrap();
        // let mut writer = BufWriter::new(file);
        // writeln!(writer, "ID {}:", expression.index).unwrap();
        // writeln!(writer, "Expression: {}", start_expression).unwrap();
        // let best_expr_str = best_expr.as_ref().map(|s| s.to_string()).unwrap_or_default();
        // writeln!(writer, "Best expression: {}", best_expr_str).unwrap();
        // writeln!(writer, "Critical Pair Rules:\n{}", picked_cp_rules).unwrap();

        info!(loggers.used_cp_rules, "ID {}:", expression.index);
        info!(loggers.used_cp_rules, "Expression: {}", start_expression);
        info!(loggers.used_cp_rules, "Best expression: {}", best_expr.clone().unwrap_or_default());
        info!(loggers.used_cp_rules, "Critical Pair Rules:\n{}", picked_cp_rules);


        // // writeln!(writer, "ID {}:", index).unwrap();
        // // writeln!(writer, "Expression: {}", start_expression).unwrap();
        // // writeln!(writer, "Best expression: {}", best_expr.clone().unwrap_or_default()).unwrap();
        // // writeln!(writer, "Critical Pair Rules:\n{}", picked_cp_rules).unwrap();
    }

    // manually serialize result structure to json and write to file

    ResultStructure::new(
        expression.index,
        start_expression.to_string(),
        "1/0".to_string(),
        result,
        best_expr.unwrap_or_default(),
        -1,
        runner.iterations.len(),
        runner.egraph.total_number_of_nodes(),
        runner.iterations.iter().map(|i| i.n_rebuilds).sum(),
        total_time,
        stop_reason,
        None,
    )
}