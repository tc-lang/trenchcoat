use super::{Token, TokenKind, Punc, Oper}

fn auto_insert_sep(tokens: &mut Vec<Token>) {
    let i = 0;
    while i < tokens.len() {
        let t = tokens[i];
        match t {
            // semi-colons become separators
            TokenKind::Punc(Punc::Semi) => tokens[i].kind = TokenKind::Punc(Punc::Sep),
            TokenKind::Punc(Punc::Newline) => {
                if let Some(next_token) = tokens[i+1] {
                    match next_token.kind {
                        // multiple newlines in a row become 1 newline
                        TokenKind::Punc(Punc::Newline) => {
                            tokens.remove(i);
                            continue;
                        },
                        // newlines before an operator which is allowed to create a newline
                        // disappear
                        TokenKind::Oper(op) => {
                            if op.newline_prefix_allowed() {
                                tokens.remove(i);
                                continue;
                            }
                        },
                        _ => (),
                    }
                }
                if let Some(prev_token) = tokens[i-1] {
                    match prev_token {
                        // newlines after commas disapear
                        TokenKind::Punc(Punc::Comma) {
                            tokens.remove(i);
                            continue;
                        },
                        // newlines after some operators disapear too
                        TokenKind::Oper(op) = prev_token.kind => {
                            if op.newline_postfix_allowed() {
                                tokens.remove(i);
                                continue;
                            }
                        },
                        _ => (),
                    }
                }
                // remaining newlines turn in to seps
                tokens[i].kind = TokenKind::Punc(Punc::Sep);
            },
            _ => ()
        }
    }
}
