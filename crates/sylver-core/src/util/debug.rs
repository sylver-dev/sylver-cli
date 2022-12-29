use std::cmp::max;

use itertools::Itertools;

pub fn render_table<C: ToString, L: ToString, Lines: IntoIterator<Item = L>>(
    columns: impl IntoIterator<Item = C>,
    lines: impl IntoIterator<Item = Lines>,
) -> String {
    let columns_repr: Vec<String> = columns.into_iter().map(|c| c.to_string()).collect();
    let lines_repr: Vec<Vec<String>> = lines
        .into_iter()
        .map(|line| line.into_iter().map(|l| l.to_string()).collect::<Vec<_>>())
        .collect();

    let columns_width: Vec<usize> = (0..columns_repr.len())
        .map(|i| {
            max(
                columns_repr[i].len() + 2,
                lines_repr
                    .iter()
                    .map(|l| l[i].len() + 2)
                    .max()
                    .unwrap_or_default(),
            )
        })
        .collect();

    let sep_line = format!(
        "+{}+",
        columns_width.iter().map(|&w| "-".repeat(w)).join("+")
    );

    let mut result = sep_line.clone();

    result.push('\n');
    result.push_str(&render_line(&columns_repr, &columns_width));

    result.push('\n');
    result.push_str(&sep_line);

    for line in lines_repr {
        result.push('\n');
        result.push_str(&render_line(&line, &columns_width));

        result.push('\n');
        result.push_str(&sep_line);
    }

    result
}

fn render_line(data: &[String], widths: &[usize]) -> String {
    format!(
        "|{}|",
        data.iter()
            .zip(widths)
            .map(|(txt, &w)| center_txt(txt, w))
            .join("|")
    )
}

fn center_txt(txt: &str, width: usize) -> String {
    if txt.len() >= width {
        txt.to_string()
    } else {
        let oversize = width - txt.len();
        let left = oversize / 2;
        let right = width - (txt.len() + left);
        format!("{}{txt}{}", " ".repeat(left), " ".repeat(right))
    }
}

#[cfg(test)]
pub mod test {
    use super::*;

    use indoc::indoc;

    #[test]
    fn render_table_alice_bob() {
        let column_names = vec!["name", "age"];
        let values = vec![vec!["Alicia", "43"], vec!["Bob", "53"]];

        let expected = indoc!(
            "\
            +--------+-----+
            |  name  | age |
            +--------+-----+
            | Alicia | 43  |
            +--------+-----+
            |  Bob   | 53  |
            +--------+-----+"
        );
        assert_eq!(expected, &render_table(column_names, values));
    }
}
