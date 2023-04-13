use build_deps;

fn main() {
    build_deps::rerun_if_changed_paths("res/**/test_config.json").unwrap();
    build_deps::rerun_if_changed_paths("res/*").unwrap();
}
