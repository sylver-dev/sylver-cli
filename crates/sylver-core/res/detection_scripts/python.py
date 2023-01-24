import os
import re

VENV_PATTERN = re.compile(r'^\.venv$')
PY_PATTERN = re.compile(r'^.*\.py$')
PYPROJECT_PATTERN = re.compile(r'^pyproject\.toml$')
POETRY_PATTERN = re.compile(r'^poetry\.toml$')

PATTERNS = [
    VENV_PATTERN,
    PY_PATTERN,
    PYPROJECT_PATTERN,
    POETRY_PATTERN,
]


def detect_projects(root):
    projects = []
    add_project_if_match(projects, root, root)
    return projects


def add_project_if_match(projects, detection_root, current_path):
    if not os.path.isdir(current_path):
        return

    childs = os.listdir(current_path)

    if any(matches_python_patterns(name) for name in childs):
        project_root = os.path.relpath(current_path, detection_root)
        projects.append({"root": project_root, "include": ["*.py"], "exclude": [".venv"]})
        return

    for child in childs:
        add_project_if_match(projects, detection_root, os.path.join(current_path, child))


def matches_python_patterns(name):
    return any(pattern.match(name) for pattern in PATTERNS)
