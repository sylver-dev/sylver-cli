use indicatif::{ProgressBar, ProgressStyle};
use std::time::Duration;

use super::*;

#[derive(Debug, Clone, Default)]
pub struct FancyLogger {}

impl Logger for FancyLogger {
    fn scoped(&self, msg: &str, done_msg: Option<&str>) -> Box<dyn ScopedMsg> {
        Box::new(FancyScoped::new(msg, done_msg))
    }

    fn error(&self, msg: &str) {
        eprintln!("❗️{}", yansi::Paint::red(msg));
    }

    fn success(&self, msg: &str) {
        println!("✓ {}", yansi::Paint::green(msg));
    }

    fn important(&self, msg: &str) {
        println!("{}", yansi::Paint::blue(msg));
    }

    fn info(&self, msg: &str) {
        println!("{}", msg);
    }
}

#[derive(Debug, Clone)]
pub struct FancyScoped {
    pb: ProgressBar,
    done_msg: Option<String>,
}

impl FancyScoped {
    pub fn new(msg: &str, done_msg: Option<&str>) -> FancyScoped {
        let pb = ProgressBar::new_spinner();
        pb.enable_steady_tick(Duration::from_millis(120));
        pb.set_style(
            ProgressStyle::with_template("{spinner} {msg}")
                .unwrap()
                .tick_strings(&["▁", "▃", "▄", "▅", "▆", "▇", "▆", "▅", "▄", "▃"]),
        );
        pb.set_message(msg.to_string());

        FancyScoped {
            pb,
            done_msg: done_msg.map(|msg| msg.to_string()),
        }
    }
}

impl Drop for FancyScoped {
    fn drop(&mut self) {
        if let Some(msg) = self.done_msg.take() {
            self.pb.finish_with_message(msg);
        } else {
            self.pb.finish()
        }
    }
}

impl ScopedMsg for FancyScoped {}
