use crate::rewrite2 as rw;
use crate::simplify::{ConditionRewrite, ExtendedCondition};
// pub type Rewrite = ConditionRewrite<Math, ConstantFold>;
use egg::{Analysis, Condition, Id, Language, Subst, Symbol, Var, define_language};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::sync::Arc;

pub type EGraph = egg::EGraph<Math, ConstantFold>;
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















pub fn rules() -> Vec<Rewrite> {
    let mut rules = Vec::new();
    rules.extend(add());
    rules.extend(and());
    rules.extend(andor());
    rules.extend(div());
    rules.extend(eq());
    rules.extend(ineq());
    rules.extend(lt());
    rules.extend(max());
    rules.extend(min());
    rules.extend(modulo());
    rules.extend(mul());
    rules.extend(not());
    rules.extend(or());
    rules.extend(sub());
    return rules;
}


pub fn add() -> Vec<Rewrite> {
    vec![
        // ADD RULES
        rw!("add-comm"      ; "(+ ?a ?b)"                   => "(+ ?b ?a)"),
        rw!("add-assoc"     ; "(+ ?a (+ ?b ?c))"            => "(+ (+ ?a ?b) ?c)"),
        rw!("add-zero"      ; "(+ ?a 0)"                    => "?a"),
        rw!("add-dist-mul"  ; "(* ?a (+ ?b ?c))"            => "(+ (* ?a ?b) (* ?a ?c))"),
        rw!("add-fact-mul"  ; "(+ (* ?a ?b) (* ?a ?c))"     => "(* ?a (+ ?b ?c))"),
        //FOLD
        rw!("add-const"     ; "( + (* ?x ?a) (* ?y ?b))"    => "( * (+ (* ?x (/ ?a ?b)) ?y) ?b)" if crate::math::compare_c0_c1("?a", "?b", "%0")),
        // rw!("sub-const-denom-1"; "( - ( / ( + ?x ?y ) ?a ) ( / ( + ?x ?b ) ?a ) )" => "( / ( + ( % ( + ?x ( % ?b ?a ) ) ?a ) ( - ?y ?b ) ) ?a )" if crate::math::is_not_zero("?a")),
        // rw!("sub-const-denom-2"; "( - ( / ( + ?x ?c1 ) ?c0 ) ( / ( + ?x ?y ) ?c0 ) )" => "( / ( - ( - (- ( + ?c0 ?c1 ) 1 ) ?y ) ( % ( + ?x ( % ?c1 ?c0 ) ) ?c0 ) ) ?c0 )" if crate::math::is_const_pos("?c0")),

        // INCONSISTENT
        // rw!("add-denom-div" ; "(/ (+ ?a (* ?b ?c)) ?b)"     => "(+ (/ ?a ?b) ?c)" if crate::math::is_not_zero("?b")),
        // rw!("add-denom-mul" ; "(+ (/ ?a ?b) ?c)"            => "(/ (+ ?a (* ?b ?c)) ?b)" if crate::math::is_not_zero("?b")),
        // rw!("add-div-mod"   ; "( + ( / ?x 2 ) ( % ?x 2 ) )" => "( / ( + ?x 1 ) 2 )"),
    ]
}

pub fn and() -> Vec<Rewrite> {
    vec![
        // AND RULES
        rw!("and-comm"          ;  "(&& ?y ?x)"                         => "(&& ?x ?y)"),
        rw!("and-assoc"         ;  "(&& ?a (&& ?b ?c))"                 => "(&& (&& ?a ?b) ?c)"),
        rw!("and-x-1"           ;  "(&& 1 ?x)"                          => "?x"),
        rw!("and-x-x"           ;  "(&& ?x ?x)"                         => "?x"),
        rw!("and-x-not-x"       ;  "(&& ?x (! ?x))"                     => "0"),
        rw!("and-eq-eq"         ;  "( && ( == ?x ?c0 ) ( == ?x ?c1 ) )" => "0" if crate::math::compare_c0_c1("?c1", "?c0", "!=")),
        rw!("and-ineq-eq"       ;  "( && ( != ?x ?c0 ) ( == ?x ?c1 ) )" => "( == ?x ?c1 )" if crate::math::compare_c0_c1("?c1", "?c0", "!=")),
        rw!("and-lt-to-min"     ;  "(&& (< ?x ?y) (< ?x ?z))"           => "(< ?x (min ?y ?z))"),
        rw!("and-min-to-lt"     ;  "(< ?x (min ?y ?z))"                 => "(&& (< ?x ?y) (< ?x ?z))"),
        rw!("and-eqlt-to-min"   ;  "(&& (<= ?x ?y) (<= ?x ?z))"         => "(<= ?x (min ?y ?z))"),
        rw!("and-min-to-eqlt"   ;  "(<= ?x (min ?y ?z))"                => "(&& (<= ?x ?y) (<= ?x ?z))"),
        rw!("and-lt-to-max"     ;  "(&& (< ?y ?x) (< ?z ?x))"           => "(< (max ?y ?z) ?x)"),
        rw!("and-max-to-lt"     ;  "(> ?x (max ?y ?z))"                 => "(&& (< ?z ?x) (< ?y ?x))"),
        rw!("and-eqlt-to-max"   ;  "(&& (<= ?y ?x) (<= ?z ?x))"         => "(<= (max ?y ?z) ?x)"),
        rw!("and-max-to-eqlt"   ;  "(>= ?x (max ?y ?z))"                => "(&& (<= ?z ?x) (<= ?y ?x))"),
        rw!("and-lt-gt-to-0"    ; "( && ( < ?c0 ?x ) ( < ?x ?c1 ) )"    => "0" if crate::math::compare_c0_c1("?c1", "?c0", "<=+1")),
        rw!("and-eqlt-eqgt-to-0"; "( && ( <= ?c0 ?x ) ( <= ?x ?c1 ) )"  => "0" if crate::math::compare_c0_c1("?c1", "?c0", "<")),
        rw!("and-eqlt-gt-to-0"  ; "( && ( <= ?c0 ?x ) ( < ?x ?c1 ) )"   => "0" if crate::math::compare_c0_c1("?c1", "?c0", "<=")),
    ]
}

pub fn andor() -> Vec<Rewrite> {
    vec![
        // AND-OR RULES
        rw!("and-over-or"   ;  "(&& ?a (|| ?b ?c))"        => "(|| (&& ?a ?b) (&& ?a ?c))"),
        rw!("or-over-and"   ;  "(|| ?a (&& ?b ?c))"        => "(&& (|| ?a ?b) (|| ?a ?c))"),
        rw!("or-x-and-x-y"  ;  "(|| ?x (&& ?x ?y))"        => "?x"),
    ]
}

pub fn custom() -> Vec<Rewrite> {
    vec![
        // // new rules
        // rw!("lt-mul"     ; "(< ?a (* ?b ( min ?c ?d)))" => "(&& (< ?a (* ?b ?c)) (< ?a (* ?b ?d)) )"  if crate::math::is_const_pos("?b")),
        // rw!("mod-min"     ; "(% ?a ?b)" => "(min (+ ?b -1 ) (% ?a ?b))"  if crate::math::is_const_pos("?b")),
        // rw!("mod-max"     ; "(% ?a ?b)" => "(max (- 1 ?b) (% ?a ?b))"  if crate::math::is_const_pos("?b")),

        // // range same, range congruence div/add exists

        // rw!("div-mul-reduce"; "(/ (* ?a ?x) ?b)" => "(+ (* (/ ?a ?b) ?x) (/ (* (% ?a ?b) ?x) ?b))" if crate::math::CompareCondition::new(vec!["?a", "?b"], |vals| vals["?a"].abs() >= vals["?b"].abs() && vals["?b"] != 0)),

        // rw!("eq-div-to-ineq-pos"; "(== (/ ?x ?c) ?k)" => "(&& (<= (* ?k ?c) ?x) (< ?x (+ (* ?k ?c) ?c)))" if crate::math::is_const_pos("?c") if crate::math::is_const_pos("?k")),

        // // not needed
        // // rw!("eq-div-to-ineq-neg"; "(== (/ ?x ?c) ?k)" => "(&& (< (- (* ?k ?c) ?c) ?x) (<= ?x (* ?k ?c)))" if crate::math::CompareCondition::new(vec!["?c", "?k"], |vals| vals["?c"] > 0 && vals["?k"] < 0)),
        // // rw!("eq-div-to-ineq-neg"; "(== (/ ?x ?c) ?k)" => "(&& (< (+ (* ?k ?c) ?c) ?x) (<= ?x (* ?k ?c)))" if crate::math::CompareCondition::new(vec!["?c", "?k"], |vals| vals["?c"] < 0 && vals["?k"] > 0)),


        // rw!("lt-mul-const-pos"; "(< (* ?c ?x) ?k)" => "(<= ?x (/ (- ?k 1) ?c))" if crate::math::CompareCondition::new(vec!["?c", "?k"], |vals| vals["?c"] > 0 && vals["?k"] > 0)),

        // // not implied => needed
        // rw!("lt-mul-const-neg"; "(< (* ?c ?x) ?k)" => "(<= ?x (/ (- ?k ?c) ?c))" if crate::math::CompareCondition::new(vec!["?c", "?k"], |vals| vals["?c"] > 0 && vals["?k"] <= 0)),

        // // rw!("lt-mul-const-pos"; "(< (* ?c ?x) ?k)" => "(< ?x (+ (/ ?k ?c) 1))" if crate::math::is_const_pos("?c")), 

        // // TODO: we need something like this
        // // rw!("div-add-reduce"; "(/ (+ ?x ?c) ?k)" => "(+ (/ ?c ?k) (/ (+ ?x (% ?c ?k)) ?k) )" if crate::math::CompareCondition::new(vec!["?a", "?b"], |vals| vals["?a"].abs() >= vals["?b"].abs() && vals["?b"] != 0)),
    ]
}

pub fn div() -> Vec<Rewrite> {
    vec![
        //DIV RULES
        rw!("div-zero"      ; "(/ 0 ?x)"            => "(0)" if crate::math::is_not_zero("?x")),
        rw!("div-cancel"    ; "(/ ?a ?a)"           => "1" if crate::math::is_not_zero("?a")),
        rw!("div-minus-down"; "(/ (* -1 ?a) ?b)"    => "(/ ?a (* -1 ?b))" if crate::math::is_not_zero("?b")),
        rw!("div-minus-up"  ; "(/ ?a (* -1 ?b))"    => "(/ (* -1 ?a) ?b)" if crate::math::is_not_zero("?b")),
        rw!("div-minus-in"  ; "(* -1 (/ ?a ?b))"    => "(/ (* -1 ?a) ?b)" if crate::math::is_not_zero("?b")),
        rw!("div-minus-out" ; "(/ (* -1 ?a) ?b)"    => "(* -1 (/ ?a ?b))" if crate::math::is_not_zero("?b")),
        //FOLD
        rw!("div-consts-div"; "( / ( * ?x ?a ) ?b )" => "( / ?x ( / ?b ?a ) )" if crate::math::compare_c0_c1("?b", "?a", "%0<0")),
        rw!("div-consts-mul"; "( / ( * ?x ?a ) ?b )" => "( * ?x ( / ?a ?b ) )" if crate::math::compare_c0_c1("?a", "?b", "%0<")),


        // INCONSISTENT
        // rw!("div-consts-add"; "( / ( + ( * ?x ?a ) ?y ) ?b )" => "( + ( * ?x ( / ?a ?b ) ) ( / ?y ?b ) )" if crate::math::compare_c0_c1("?a", "?b", "%0<")),
        // rw!("div-separate"  ; "( / ( + ?x ?a ) ?b )" => "( + ( / ?x ?b ) ( / ?a ?b ) )" if crate::math::compare_c0_c1("?a", "?b", "%0<")),
    ]
}

pub fn eq() -> Vec<Rewrite> {
    vec![
        // Equality RULES
        rw!("eq-comm"       ; "(== ?x ?y)"           => "(== ?y ?x)"),
        rw!("eq-x-y-0"      ; "(== ?x ?y)"           => "(== (- ?x ?y) 0)"),
        rw!("eq-swap"       ; "(== (+ ?x ?y) ?z)"    => "(== ?x (- ?z ?y))"),
        rw!("eq-x-x"        ; "(== ?x ?x)"           => "1"),
        rw!("eq-mul-x-y-0"  ; "(== (* ?x ?y) 0)"     => "(|| (== ?x 0) (== ?y 0))"),
        rw!("eq-max-lt"     ; "( == (max ?x ?y) ?y)" => "(<= ?x ?y)"),
        rw!("Eq-min-lt"     ; "( == (min ?x ?y) ?y)" => "(<= ?y ?x)"),
        rw!("Eq-lt-min"     ; "(<= ?y ?x)"           => "( == (min ?x ?y) ?y)"),
        rw!("Eq-a-b"        ; "(== (* ?a ?x) ?b)"    => "0" if crate::math::compare_c0_c1("?b", "?a", "!%0")),
        rw!("Eq-max-c-pos"  ; "(== (max ?x ?c) 0)"   => "0" if crate::math::is_const_pos("?c")),
        rw!("Eq-max-c-neg"  ; "(== (max ?x ?c) 0)"   => "(== ?x 0)" if crate::math::is_const_neg("?c")),
        rw!("Eq-min-c-pos"  ; "(== (min ?x ?c) 0)"   => "0" if crate::math::is_const_neg("?c")),
        rw!("Eq-min-c-neg"  ; "(== (min ?x ?c) 0)"   => "(== ?x 0)" if crate::math::is_const_pos("?c")),
    ]
}

pub fn ineq() -> Vec<Rewrite> {
    vec![
        // Inequality RULES
        rw!("ineq-to-eq";  "(!= ?x ?y)"        => "(! (== ?x ?y))"),
    ]
}

pub fn lt() -> Vec<Rewrite> {
    vec![
        // LT RULES
        rw!("gt-to-lt"      ;  "(> ?x ?z)"              => "(< ?z ?x)"),
        rw!("lt-swap"      ;  "(< ?x ?y)"              => "(< (* -1 ?y) (* -1 ?x))"),
        rw!("lt-to-zero"    ;  "(< ?a ?a)"              => "0"),
        rw!("lt-swap-in"    ;  "(< (+ ?x ?y) ?z)"       => "(< ?x (- ?z ?y))" ),
        rw!("lt-swap-out"   ;  "(< ?z (+ ?x ?y))"       => "(< (- ?z ?y) ?x)" ),
        rw!("lt-x-x-sub-a"  ;  "(< (- ?a ?y) ?a )"      => "1" if crate::math::is_const_pos("?y")),
        rw!("lt-const-pos"  ;  "(< 0 ?y )"              => "1" if crate::math::is_const_pos("?y")),
        rw!("lt-const-neg"  ;  "(< ?y 0 )"              => "1" if crate::math::is_const_neg("?y")),
        rw!("min-lt-cancel" ;  "( < ( min ?x ?y ) ?x )" => "( < ?y ?x )"),
        rw!("lt-min-mutual-term"    ; "( < ( min ?z ?y ) ( min ?x ?y ) )"           => "( < ?z ( min ?x ?y ) )"),
        rw!("lt-max-mutual-term"    ; "( < ( max ?z ?y ) ( max ?x ?y ) )"           => "( < ( max ?z ?y ) ?x )"),
        rw!("lt-min-term-term+pos"  ; "( < ( min ?z ?y ) ( min ?x ( + ?y ?c0 ) ) )" => "( < ( min ?z ?y ) ?x )" if crate::math::is_const_pos("?c0")),
        rw!("lt-max-term-term+pos"  ; "( < ( max ?z ( + ?y ?c0 ) ) ( max ?x ?y ) )" => "( < ( max ?z ( + ?y ?c0 ) ) ?x )" if crate::math::is_const_pos("?c0")),
        rw!("lt-min-term+neg-term"  ; "( < ( min ?z ( + ?y ?c0 ) ) ( min ?x ?y ) )" => "( < ( min ?z ( + ?y ?c0 ) ) ?x )" if crate::math::is_const_neg("?c0")),
        rw!("lt-max-term+neg-term"  ; "( < ( max ?z ?y ) ( max ?x ( + ?y ?c0 ) ) )" => "( < ( max ?z ?y ) ?x )" if crate::math::is_const_neg("?c0")),
        rw!("lt-min-term+cpos"      ; "( < ( min ?x ?y ) (+ ?x ?c0) )"              => "1" if crate::math::is_const_pos("?c0")),
        rw!("lt-min-max-cancel"     ; "(< (max ?a ?c) (min ?a ?b))"                 => "0"),
        // rw!("lt-mul-pos-cancel"     ; "(< (* ?x ?y) ?z)"                            => "(< ?x (/ ?z ?y))"  if crate::math::is_const_pos("?y")),
        // rw!("lt-mul-div-cancel"     ; "(< ?x (/ ?z ?y))"                            => "(< (* ?x ?y) ?z))"  if crate::math::is_const_pos("?y")),
        rw!("lt-const-mod"     ; "(< ?a (% ?x ?b))" => "1"  if crate::math::compare_c0_c1("?a", "?b", "<=-a")),
        rw!("lt-const-mod-false"     ; "(< ?a (% ?x ?b))" => "0"  if crate::math::compare_c0_c1("?a", "?b", ">=a")),

        // INCONSISTENT
        // rw!("lt-mul-pos-cancel"     ; "(< (* ?x ?y) ?z)"                            => "(< ?x ( / (- ( + ?z ?y ) 1 ) ?y ) )"  if crate::math::is_const_pos("?y")),
        // rw!("lt-mul-div-cancel"     ; "(< ?y (/ ?x ?z))"                            => "( < ( - ( * ( + ?y 1 ) ?z ) 1 ) ?x )"  if crate::math::is_const_pos("?z")),
    ]
}

pub fn max() -> Vec<Rewrite> { vec![
    // MAX RULES
    rw!("max-to-min"; "(max ?a ?b)" => "(* -1 (min (* -1 ?a) (* -1 ?b)))"),
    // rw!("min-to-max"; "(min ?a ?b)" => "(* -1 (max (* -1 ?a) (* -1 ?b)))"),
    
]}

pub fn min() -> Vec<Rewrite> {
    vec![
        // MIN RULES
        rw!("min-comm"      ; "(min ?a ?b)"                         => "(min ?b ?a)"),
        rw!("min-ass"       ; "(min (min ?x ?y) ?z)"                => "(min ?x (min ?y ?z))"),
        rw!("min-x-x"       ; "(min ?x ?x)"                         => "?x"),
        rw!("min-max"       ; "(min (max ?x ?y) ?x)"                => "?x"),
        rw!("min-max-max-x" ; "(min (max ?x ?y) (max ?x ?z))"       => "(max (min ?y ?z) ?x)"),
        rw!("min-max-min-y" ; "(min (max (min ?x ?y) ?z) ?y)"       => "(min (max ?x ?z) ?y)"),
        rw!("min-sub-both"  ; "(min (+ ?a ?b) ?c)"                  => "(+ (min ?b (- ?c ?a)) ?a)"),
        rw!("min-add-both"  ; "(+ (min ?x ?y) ?z)"                  => "(min (+ ?x ?z) (+ ?y ?z))"),
        rw!("min-x-x-plus-a-pos"; "(min ?x (+ ?x ?a))"               => "?x" if crate::math::is_const_pos("?a") ),
        rw!("min-x-x-plus-a-neg"; "(min ?x (+ ?x ?a))"               => "(+ ?x ?a)" if crate::math::is_const_neg("?a") ),
        rw!("min-mul-in-pos"    ; "(* (min ?x ?y) ?z)"               => "(min (* ?x ?z) (* ?y ?z))" if crate::math::is_const_pos("?z")),
        rw!("min-mul-out-pos"   ; "(min (* ?x ?z) (* ?y ?z))"        => "(* (min ?x ?y) ?z)"  if crate::math::is_const_pos("?z")),
        rw!("min-mul-in-neg"    ; "(* (min ?x ?y) ?z)"               => "(max (* ?x ?z) (* ?y ?z))" if crate::math::is_const_neg("?z")),
        rw!("min-mul-out-neg"   ; "(max (* ?x ?z) (* ?y ?z))"        => "(* (min ?x ?y) ?z)" if crate::math::is_const_neg("?z")),
        rw!("min-div-in-pos"    ; "(/ (min ?x ?y) ?z)"               => "(min (/ ?x ?z) (/ ?y ?z))" if crate::math::is_const_pos("?z")),
        rw!("min-div-out-pos"   ; "(min (/ ?x ?z) (/ ?y ?z))"        => "(/ (min ?x ?y) ?z)" if crate::math::is_const_pos("?z")),
        rw!("min-div-in-neg"    ; "(/ (max ?x ?y) ?z)"               => "(min (/ ?x ?z) (/ ?y ?z))"  if crate::math::is_const_neg("?z")),
        rw!("min-div-out-neg"   ; "(min (/ ?x ?z) (/ ?y ?z))"        => "(/ (max ?x ?y) ?z)" if crate::math::is_const_neg("?z")),
        rw!("min-max-const"     ; "( min ( max ?x ?c0 ) ?c1 )"       => "?c1" if crate::math::compare_c0_c1("?c1","?c0","<=")),
        rw!("min-mod-const-to-mod"      ; "(min (% ?x ?c0) ?c1)"                         => "(% ?x ?c0)" if crate::math::compare_c0_c1("?c1","?c0",">=a-1")),
        rw!("min-mod-const-to-const"    ; "(min (% ?x ?c0) ?c1)" => "?c1" if crate::math::compare_c0_c1("?c1","?c0","<=-a+1")), // c1 <= - |c0| + 1
        rw!("min-max-switch"            ; "( min ( max ?x ?c0 ) ?c1 )" => "( max ( min ?x ?c1 ) ?c0 )" if crate::math::compare_c0_c1("?c0","?c1","<=") ),
        rw!("max-min-switch"            ; "( max ( min ?x ?c1 ) ?c0 )" => "( min ( max ?x ?c0 ) ?c1 )" if crate::math::compare_c0_c1("?c0","?c1","<=") ),
        //FOLD
        rw!("min-consts-or"          ; "( < ( min ?y ?c0 ) ?c1 )" => "( || ( < ?y ?c1 ) ( < ?c0 ?c1 ) )"),
        rw!("max-consts-and"         ; "( < ( max ?y ?c0 ) ?c1 )" => "( && ( < ?y ?c1 ) ( < ?c0 ?c1 ) )"),
        rw!("max-consts-or"          ; "( < ?c1 ( max ?y ?c0 ) )" => "( || ( < ?c1 ?y ) ( < ?c1 ?c0 ) )"),
        rw!("min-consts-div-pos"     ; "( min ( * ?x ?a ) ?b )" => "( * ( min ?x ( / ?b ?a ) ) ?a )" if crate::math::compare_c0_c1("?b", "?a", "%0<") ), // b%a==0 && 0<b        
        rw!("min-min-div-pos"        ; "( min ( * ?x ?a ) ( * ?y ?b ) )" => "( * ( min ?x ( * ?y ( / ?b ?a ) ) ) ?a )" if crate::math::compare_c0_c1("?b", "?a", "%0<") ),  
        rw!("min-consts-div-neg"     ; "( min ( * ?x ?a ) ?b )" => "( * ( max ?x ( / ?b ?a ) ) ?a )" if crate::math::compare_c0_c1("?b", "?a", "%0>") ),  
        rw!("min-min-div-neg"        ; "( min ( * ?x ?a ) ( * ?y ?b ) )" => "( * ( max ?x ( * ?y ( / ?b ?a ) ) ) ?a )" if crate::math::compare_c0_c1("?b", "?a", "%0>") ), 

        // INCONSISTENT
        // rw!("min-div-mul"               ; "( min ( * ( / ?x ?c0 ) ?c0 ) ?x )"    => "( * ( / ?x ?c0 ) ?c0 )" if  crate::math::is_const_pos("?c0")),
    ]
}

pub fn modulo() -> Vec<Rewrite> {
    // let r1 =         rw!("mod-zero"      ; "(% 0 ?x)"             => "0" if crate::math::IsNotZeroCondition::new("?x"));

    vec![
        //MOD RULES
        rw!("mod-zero"      ; "(% 0 ?x)"             => "0" if crate::math::IsNotZeroCondition::new("?x")),
        rw!("mod-x-x"       ; "(% ?x ?x)"            => "0" if crate::math::is_not_zero("?x")),
        rw!("mod-one"       ; "(% ?x 1)"             => "0"),
        rw!("mod-minus-out" ; "(% (* ?x -1) ?c)"     => "(* -1 (% ?x ?c))" if crate::math::is_not_zero("?c")),
        rw!("mod-minus-in"  ; "(* -1 (% ?x ?c))"     => "(% (* ?x -1) ?c)" if crate::math::is_not_zero("?c")),
        //FOLD
        rw!("mod-consts"    ; "( % ( + ( * ?x ?c0 ) ?y ) ?c1 )" => "( % ?y ?c1 )" if crate::math::compare_c0_c1("?c0", "?c1", "%0")),
        rw!("mod-multiple";"(% (* ?c0 ?x) ?c1)" => "0" if crate::math::compare_c0_c1("?c0", "?c1", "%0")),

        // INCONSISTENT
        // rw!("mod-two"       ; "(% (- ?x ?y) 2)"      => "(% (+ ?x ?y) 2)"),
        // rw!("mod-const-add" ; "(% ?x ?c1)"           => "(% (+ ?x ?c1) ?c1)" if crate::math::compare_c0_c1("?c1","?x","<=a")),
        // rw!("mod-const-sub" ; "(% ?x ?c1)"           => "(% (- ?x ?c1) ?c1)" if crate::math::compare_c0_c1("?c1","?x","<=a")),
    ]
}

pub fn mul() -> Vec<Rewrite> {
    vec![
        //MUL RULES
        rw!("mul-comm"      ; "(* ?a ?b)"                   => "(* ?b ?a)"),
        rw!("mul-assoc"     ; "(* ?a (* ?b ?c))"            => "(* (* ?a ?b) ?c)"),
        rw!("mul-zero"      ; "(* ?a 0)"                    => "0"),
        rw!("mul-one"       ; "(* ?a 1)"                    => "?a"),
        rw!("mul-cancel-div"; "(* (/ ?a ?b) ?b)"            => "(- ?a (% ?a ?b))" if crate::math::is_not_zero("?b")),
        rw!("mul-max-min"   ; "(* (max ?a ?b) (min ?a ?b))" => "(* ?a ?b)"),
        rw!("div-cancel-mul"; "(/ (* ?y ?x) ?x)"            => "?y" if crate::math::is_not_zero("?x")),
    ]
}

pub fn not() -> Vec<Rewrite> {
    vec![
        // NOT RULES
        rw!("eqlt-to-not-gt";  "(<= ?x ?y)"     => "(! (< ?y ?x))" ),
        rw!("not-gt-to-eqlt";  "(! (< ?y ?x))"  => "(<= ?x ?y)" ),
        rw!("eqgt-to-not-lt";  "(>= ?x ?y)"     => "(! (< ?x ?y))" ),
        rw!("not-eq-to-ineq";  "(! (== ?x ?y))" => "(!= ?x ?y)" ),
        rw!("not-not"       ;  "(! (! ?x))"     => "?x" ),
    ]
}

pub fn or() -> Vec<Rewrite> {
    vec![
        // OR RULES
        rw!("or-to-and" ;"(|| ?x ?y)"        => "(! (&& (! ?x) (! ?y)))"),
        rw!("or-comm"   ;"(|| ?y ?x)"        => "(|| ?x ?y)"),
    ]
}

pub fn sub() -> Vec<Rewrite> {
    vec![
        // SUB RULES
        rw!("sub-to-add"; "(- ?a ?b)"   => "(+ ?a (* -1 ?b))"),
        // rw!("add-to-sub"; "(+ ?a ?b)"   => "(- ?a (* -1 ?b))"),
    ]
}










