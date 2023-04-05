import path
import os
import re

YAML_PATTERN = re.compile(r'^.*\.(yaml|yml)$')

PATTERNS = [
    YAML_PATTERN
]


def detect_projects(root):
    projects = []
    add_project_if_match(projects, root, root)
    return projects


def add_project_if_match(projects, detection_root, current_path):
    if not path.isdir(current_path):
        return

    childs = os.listdir(current_path)

    if any(matches_yaml_patterns(name) for name in childs):
        project_root = path.relpath(current_path, detection_root)
        projects.append({"root": project_root, "include": ["**/*.yaml", "**/*.yml"], "exclude": []})
        return

    for child in childs:
        add_project_if_match(projects, detection_root, path.join(current_path, child))


def matches_yaml_patterns(name):
    return any(pattern.match(name) for pattern in PATTERNS)
