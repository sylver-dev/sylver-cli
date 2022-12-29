use std::{
    cmp::Ordering,
    fmt::{self, Display, Formatter},
};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct InclPosRange {
    start: Pos,
    end: Pos,
}

impl InclPosRange {
    pub fn new(start: Pos, end: Pos) -> Option<InclPosRange> {
        if end >= start {
            Some(InclPosRange { start, end })
        } else {
            None
        }
    }

    pub fn start(&self) -> Pos {
        self.start
    }

    pub fn end(&self) -> Pos {
        self.end
    }

    pub fn line_range(&self) -> (usize, usize) {
        (self.start.line, self.end.line)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Pos {
    /// Current line
    pub line: usize,
    /// Current column
    pub col: usize,
    /// Index of the current char in the parsed String
    pub txt_pos: usize,
}

impl Pos {
    /// Create a new Pos with the given line, column and text position.
    pub fn new((line, col): (usize, usize), txt_pos: usize) -> Pos {
        Pos { line, col, txt_pos }
    }

    pub fn line(&self) -> usize {
        self.line
    }

    pub fn add_to_line(self, n: usize) -> Pos {
        Pos {
            line: self.line + n,
            ..self
        }
    }

    pub fn set_col(self, col: usize) -> Pos {
        Pos { col, ..self }
    }

    pub fn add_to_col(self, n: usize) -> Pos {
        Pos {
            col: self.col + n,
            ..self
        }
    }

    pub fn add_to_text_pos(self, n: usize) -> Pos {
        Pos {
            txt_pos: self.txt_pos + n,
            ..self
        }
    }

    pub fn col(&self) -> usize {
        self.col
    }

    pub fn txt_pos(&self) -> usize {
        self.txt_pos
    }
}

impl Ord for Pos {
    fn cmp(&self, other: &Self) -> Ordering {
        self.txt_pos.cmp(&other.txt_pos)
    }
}

impl PartialOrd for Pos {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.txt_pos.cmp(&other.txt_pos))
    }
}

impl Default for Pos {
    fn default() -> Self {
        Pos {
            line: 1,
            col: 1,
            txt_pos: 0,
        }
    }
}

impl Display for Pos {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}
