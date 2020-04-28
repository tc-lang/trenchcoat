use super::{Oper, Punc, Token, TokenKind};

/// Transform a token tree containing `Punc::Semi` and `Punc::Newline`s to a token tree containing
/// `Punc::Sep`s.
pub fn auto_insert_sep(tokens: &mut Vec<Token>) {
    // Here, we iterate over each token, for each we:
    //  1) Replace Punc::Semi with Puct::Sep;
    //  2) Remove Punc::Newline if it is:
    //      a) After a comma,
    //      b) before a dot,
    //      c) before an infix or postfix operator,
    //      d) after an infix or prefix operator;
    //  3) Replace remaining Punc::Newline tokens with Punc::Sep.
    //
    //  The i variable is required since, when we remove an item, we don't want to increment
    let mut i = 0;
    while i < tokens.len() {
        match &mut tokens[i].kind {
            // recursively enter sub-trees
            TokenKind::Parens(ref mut inner_tokens) => auto_insert_sep(inner_tokens),
            TokenKind::Curlys(ref mut inner_tokens) => auto_insert_sep(inner_tokens),
            TokenKind::Squares(ref mut inner_tokens) => auto_insert_sep(inner_tokens),

            // semi-colons become separators
            TokenKind::Punc(Punc::Semi) => tokens[i].kind = TokenKind::Punc(Punc::Sep),

            TokenKind::Punc(Punc::Newline) => {
                if let Some(next_token) = tokens.get(i + 1) {
                    match next_token.kind {
                        // multiple newlines in a row become 1 newline
                        TokenKind::Punc(Punc::Newline) => {
                            tokens.remove(i);
                            continue;
                        }

                        // newlines before a . also disappear
                        TokenKind::Punc(Punc::Dot) => {
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
                        }

                        _ => (),
                    }
                }
                if let Some(prev_token) = tokens.get(i - 1) {
                    match prev_token.kind {
                        // newlines after commas disapear
                        TokenKind::Punc(Punc::Comma) => {
                            tokens.remove(i);
                            continue;
                        }

                        // newlines after some operators disapear too
                        TokenKind::Oper(op) => {
                            if op.newline_postfix_allowed() {
                                tokens.remove(i);
                                continue;
                            }
                        }

                        _ => (),
                    }
                }
                // remaining newlines turn in to seps
                tokens[i].kind = TokenKind::Punc(Punc::Sep);
            }
            _ => (),
        }
        // If we've not removed the token, then we can increment the index to the next one.
        i += 1;
    }
}
