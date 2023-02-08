import os
import re

JS_PATTERN = re.compile(r'^.*\.(js|jsx)$')
PACKAGE_PATTERN = re.compile(r'^package\.json$')

PATTERNS = [
    JS_PATTERN,
    PACKAGE_PATTERN
]


def detect_projects(root):
    projects = []
    add_project_if_match(projects, root, root)
    return projects


def add_project_if_match(projects, detection_root, current_path):
    if not os.path.isdir(current_path):
        return

    childs = os.listdir(current_path)

    if any(matches_javascript_patterns(name) for name in childs):
        project_root = os.path.relpath(current_path, detection_root)
        projects.append({"root": project_root, "include": ["**/*.js", "**/*.jsx"], "exclude": ["node_modules/*"]})
        return

    for child in childs:
        add_project_if_match(projects, detection_root, os.path.join(current_path, child))


def matches_javascript_patterns(name):
    return any(pattern.match(name) for pattern in PATTERNS)
