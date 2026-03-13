use std::ffi::OsString;
use std::io::Write;
use std::path::Path;

use chrono::Local;
use clap::Parser;
use indicatif::{ProgressBar, ProgressStyle};
use slog::info;

mod logger;
mod io;
mod structs;
mod simplify;
mod rules;
use logger::init_loggers;
use io::reader::read_expressions;

use crate::simplify::simplify_expression;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    #[arg(long, default_value = "v1", help = "Suffix for output files")]
    suffix: String,

    #[arg(long, default_value_t = 1000, help = "Number of egraph iterations")]
    egraph_iterations: usize,

    #[arg(long, default_value_t = 5000, help = "Max number of nodes in the egraph")]
    nodes: usize,

    #[arg(long, default_value_t = 1000, help = "EGraph time limit over all iterations in seconds")]
    total_time: u64,

    #[arg(long, default_value_t = 5, help = "Number of restart iterations to run")]
    iterations: usize,

    #[arg(long, default_value_t = 75, help = "Number of critial pairs to add to the rules")]
    cp_count: usize,

    #[arg(long, default_value_t = 10, help = "Number of critial pairs to use for critical pair computation")]
    cp_retain: usize,

    #[arg(long, default_value_t = 0, help = "Continue from this expression id")]
    continue_from: usize,

    #[arg(long, default_value = "data/prefix/evaluation.csv", help = "Path to the expression file to read from")]
    expression_file: String,
}

#[hotpath::main]
fn main() {
    let args = Args::parse();

    let log_dir = Path::new("logs");
    if !log_dir.exists() {
        std::fs::create_dir(log_dir).expect("Failed to create logs directory");
    }


    let expression_vect = read_expressions(&OsString::from(&args.expression_file)).unwrap();
    // let results = prove_expressions_pulses(&expression_vect, -1, args, true, false);
    // let mut results = Vec::new();
    // For each expression try to prove it using Caviar with Pulses and NPP then push the results into the results vector.

    let progress_bar = ProgressBar::new(expression_vect.len() as u64);
    progress_bar.set_style(
        ProgressStyle::with_template(
            // The template string:
            // {spinner}      : A spinning animation
            // {elapsed...}   : Time since the bar started
            // {bar}          : The actual progress bar
            // {pos}/{len}    : Item count
            // {per_sec}      : Processing speed
            // {eta_precise}  : Countdown timer (HH:MM:SS)
            // {end_time}     : OUR CUSTOM KEY for the absolute clock time
            "{spinner:.green} [{elapsed_precise}] {wide_bar:.cyan/blue} {pos}/{len} ({percent}%) | Speed: {per_sec} | ETA: {eta_precise} | Finishes at: {end_time} {msg}"
        )
        .unwrap()
        // Define our custom {end_time} variable
        .with_key("end_time", |state: &indicatif::ProgressState, w: &mut dyn std::fmt::Write| {
            let eta = state.eta();
            // If ETA is 0, we either just started or we are done
            if eta.as_secs() > 0 {
                // Add the ETA duration to the current local clock time
                let expected_end = Local::now() + eta;
                write!(w, "{}", expected_end.format("%H:%M:%S")).unwrap();
            } else {
                write!(w, "TBD").unwrap();
            }
        })
        // Use sleek solid blocks instead of hashes
        .progress_chars("██░") 
    );
    // progress_bar
    //     .set_style(
    //         ProgressStyle::with_template("[{elapsed_precise}] {bar:40.cyan/blue} {pos}/{len} ({percent}%)")
    //             .unwrap()
    //             .progress_chars("##-"),
    //     );
    let mut loggers = init_loggers(log_dir, &args.suffix, progress_bar.clone());

    info!(loggers.logger, "Starting Caviar CP with configuration: {:?}", args);

    writeln!(loggers.results,"index,start_expression,end_expression,result,best_expr,class,iterations,egraph_size,rebuilds,total_time,stop_reason,condition,halide_result,halide_time").unwrap();

    let mut solved = 0;

    let init_time = std::time::Instant::now();
    for expression in expression_vect.iter() {
        // rulset_class = -1
        // use_iteration_check = true
        // report = false

        let mut result = simplify_expression(
            &expression,
            &loggers,
            &args
        );

        result.add_halide(expression.halide_result.clone(), expression.halide_time);
        
        writeln!(loggers.results, "{},{},{},{},{},{},{},{},{},{},{},{},{},{}", 
            result.index,
            result.start_expression,
            result.end_expression,  
            result.result,
            result.best_expr,
            result.class,
            result.iterations,
            result.egraph_size,
            result.rebuilds,
            result.total_time,
            result.stop_reason,
            result.condition.unwrap_or("".to_string()),
            result.halide_result,
            result.halide_time
        ).unwrap();
        // results.push(result);
        if result.result {
            solved += 1;
        }

        progress_bar.inc(1);
        // progress_bar.set_message(format!("solved {}/{}", solved, progress_bar.position()));
    }

    let elapsed = init_time.elapsed();
    progress_bar.finish_with_message(format!(
        "done: solved {}/{} (elapsed: {:?})",
        solved,
        expression_vect.len(),
        elapsed
    ));

    info!(loggers.logger, "Finished proving expressions. Solved {}/{}", solved, expression_vect.len());
    // write_results(&format!("tmp/results_beh_{}.csv", threshold), &results).unwrap();


}
