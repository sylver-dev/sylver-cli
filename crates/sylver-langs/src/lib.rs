use tree_sitter::Language;

pub fn python_language() -> Language {
    tree_sitter_python::language()
}

pub fn javascript_language() -> Language {
    tree_sitter_javascript::language()
}

pub fn yaml_language() -> Language {
    tree_sitter_yaml::language()
}
