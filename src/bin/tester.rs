use std::env;
use std::fs;
use std::process;

fn check_program(program: &str) -> (bool, String) {
    let source = fs::read_to_string(program).unwrap_or_else(|_| {
        eprintln!("Couldn't open source file {}", program);
        process::exit(1);
    });

    let mut check_lines = Vec::new();
    for line in source.lines() {
        if line.starts_with("##") {
            check_lines.push(line.strip_prefix("## ").unwrap());
        }
    }

    let result = process::Command::new("cargo")
        .args(&["run", "--quiet", program])
        .output()
        .expect("failed to execute process");

    if !result.status.success() {
        return (
            false,
            format!(
                "Program failed to run. stderr:\n{}",
                String::from_utf8(result.stderr).unwrap()
            ),
        );
    }

    let expected = if !check_lines.is_empty() {
        // Extra \n since the stdout has one on the end
        check_lines.join("\n") + "\n"
    } else {
        "".to_string()
    };

    let got_stdout = String::from_utf8(result.stdout).unwrap();
    let same = if !check_lines.is_empty() {
        expected == got_stdout
    } else {
        true
    };

    (
        same,
        if same {
            "".to_string()
        } else {
            let mut report = format!("Expected:\n{}\nGot:\n{}", expected, got_stdout);
            for (l1, l2) in check_lines.iter().zip(got_stdout.lines()) {
                if *l1 != l2 {
                    report += &format!(
                        "\nDifference begins here -\n\
                                     Expected: {}\n\
                                  \x20    Got: {}\n",
                        l1, l2
                    );
                    break;
                }
            }
            report
        },
    )
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Expected test file names as arguments");
        process::exit(1);
    }

    let mut exit_code = 0;
    // 1 to skip program name
    for program in &args[1..] {
        let (passed, report) = check_program(&program);
        println!("===============================");
        println!("{}:", program);
        if passed {
            println!("PASSED");
        } else {
            println!("{}", report);
            println!("FAILED");
            exit_code = 1;
        }
    }

    process::exit(exit_code);
}
