use slog::{o, Drain, Logger, Level, LevelFilter};
use slog_term::{FullFormat, PlainSyncDecorator};
use std::{fs::{File, OpenOptions}, io::BufWriter, path::Path, sync::{Arc, Mutex}};
use indicatif::ProgressBar;
use std::io::{self, Write};

#[derive(Clone)]
pub struct IndicatifWriter {
    pb: ProgressBar,
}

impl IndicatifWriter {
    pub fn new(pb: ProgressBar) -> Self {
        Self { pb }
    }
}

impl Write for IndicatifWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.pb.suspend(|| {
            io::stdout().write_all(buf)
        })?;
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        io::stdout().flush()
    }
}


fn create_file_drain(filepath: impl AsRef<Path>, level: Level) -> impl Drain<Ok = (), Err = slog::Never> {
    let file = OpenOptions::new()
        .create(true)
        .write(true)
        .append(true)
        .open(filepath)
        .unwrap();
    
    // Use PlainDecorator for files so we don't write terminal color codes to the text file
    let decorator = slog_term::PlainDecorator::new(file);
    let drain = slog_term::FullFormat::new(decorator).build().fuse();
    let async_drain = slog_async::Async::new(drain).build().fuse();
    
    // Filter this specific drain by the requested log level
    LevelFilter::new(async_drain, level).fuse()
}

fn create_stdout_drain(level: Level) -> impl Drain<Ok = (), Err = slog::Never> {
    let decorator = slog_term::TermDecorator::new().build();
    let drain = slog_term::FullFormat::new(decorator).build().fuse();
    let async_drain = slog_async::Async::new(drain).build().fuse();
    
    LevelFilter::new(async_drain, level).fuse()
}

pub struct Loggers {
    pub logger: slog::Logger,
    pub results: BufWriter<File>,
    pub cp_rules: slog::Logger,
    pub used_cp_rules: slog::Logger,
    pub applied_rules: slog::Logger,
}

pub fn init_loggers(log_dir: &Path, suffix: &str, pb: ProgressBar) -> Loggers {
    let cp_drain = create_file_drain(format!("{}/{}_cp_rules.txt", log_dir.display(), suffix), Level::Info);
    let shared_cp_drain = Arc::new(Mutex::new(cp_drain)).fuse();

    let safe_writer = IndicatifWriter::new(pb);
    let decorator = PlainSyncDecorator::new(safe_writer);
    let stdout_drain = FullFormat::new(decorator).build().fuse();
    let stdout_drain = slog_async::Async::new(stdout_drain).build().fuse(); // Highly recommended for terminal I/O

    return Loggers {
        logger: Logger::root(
            slog::Duplicate::new(
                stdout_drain, // log to terminal
                slog::Duplicate::new(
                    create_file_drain(format!("{}/{}_log.txt", log_dir.display(), suffix), Level::Info),
                    shared_cp_drain.clone() // also log ever info to cp file
                ).fuse()
            ).fuse(),
            o!("logger" => "main")
        ),
        results: BufWriter::new(OpenOptions::new()
            .create(true)
            .write(true)
            .append(true)
            .open(format!("{}/{}_results.txt", log_dir.display(), suffix))
            .unwrap()
        ),
        // results: Logger::root(
        //     create_file_drain(format!("{}/{}_results.txt", log_dir.display(), suffix), Level::Info),
        //     o!("logger" => "results")
        // ),
        cp_rules: Logger::root(
            shared_cp_drain,
            o!("logger" => "cp_rules")
        ),
        used_cp_rules: Logger::root(
            create_file_drain(format!("{}/{}_used_cp_rules.txt", log_dir.display(), suffix), Level::Info),
            o!("logger" => "used_cp_rules")
        ),
        applied_rules: Logger::root(
            create_file_drain(format!("{}/{}_applied_rules.txt", log_dir.display(), suffix), Level::Info),
            o!("logger" => "applied_rules")
        ),
    };
}