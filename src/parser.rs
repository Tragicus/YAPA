use crate::term::*;
use std::rc::Rc;
use std::iter::Peekable;
use std::str::Chars;

#[derive(Debug, Clone, PartialEq)]
enum Token {
    Var(String),
    Lambda,
    Dot,
    Comma,
    Colon,
    Arrow,
    Pi,
    LParen,
    RParen,
    Type,
    Prop,
}

struct Lexer<'a> {
    input: Peekable<Chars<'a>>,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str) -> Self {
        Lexer {
            input: input.chars().peekable(),
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        while let Some(ch) = self.input.next() {
            return match ch {
                '.' => { Some(Token::Dot) },
                ',' => { Some(Token::Comma) },
                ':' => { Some(Token::Colon) },
                '-' => {
                    if self.input.peek() == Some(&'>') {
                        self.input.next();
                        Some(Token::Arrow)
                    } else {
                        None //Should we panic?
                    }
                },
                '(' => { Some(Token::LParen) },
                ')' => { Some(Token::RParen) },
                c if c.is_whitespace() => { continue },
                'T' if self.input.clone().take(3).collect::<String>() == "ype" => {
                    self.input.next(); // Consume "ype"
                    self.input.next(); // Consume "ype"
                    self.input.next(); // Consume "ype"
                    Some(Token::Type)
                }
                'P' if self.input.clone().take(3).collect::<String>() == "rop" => {
                    self.input.next(); // Consume "rop"
                    self.input.next(); // Consume "rop"
                    self.input.next(); // Consume "rop"
                    Some(Token::Prop)
                }
                'f' if self.input.clone().take(2).collect::<String>() == "un" => {
                    self.input.next(); // Consume "un"
                    self.input.next(); // Consume "un"
                    Some(Token::Lambda)
                }
                'f' if self.input.clone().take(5).collect::<String>() == "orall" => {
                    self.input.next(); // Consume "orall"
                    self.input.next(); // Consume "orall"
                    self.input.next(); // Consume "orall"
                    self.input.next(); // Consume "orall"
                    self.input.next(); // Consume "orall"
                    Some(Token::Pi)
                }
                c if c.is_alphanumeric() => {
                    let ident: String = c.to_string() + &self.input.by_ref().take_while(|ch| ch.is_alphanumeric()).collect::<String>();
                    Some(Token::Var(ident))
                },
                _ => { self.input.next(); None },
            };
        }
        None
    }
}

pub fn parse<'a>(input: &'a str) -> Result<Term, String> {
    parse_term(&mut Lexer::new(input).peekable())
}

/* Parser the longest possible string of input as a term. */
fn parse_term<'a>(lex: &mut Peekable<Lexer<'a>>) -> Result<Term, String> {
    let t = parse_atom(lex)?;
    match lex.peek() {
        Some(Token::Arrow) => {
            lex.next();
            Ok(Term::Pi("_".to_string(), Rc::new(t), Box::new(parse_term(lex)?)))
        }
        Some(Token::Colon) => {
            lex.next();
            parse_term(lex)?;
            Ok(t) //TODO: add a case for casts.
        }
        _ => {
            match parse_term(lex) {
                Ok(u) => Ok(t.mk_app(u)),
                _ => Ok(t)
            }
        }
    }
}

/* Parser the shortest possible string of input as a term. */
fn parse_atom<'a>(lex: &mut Peekable<Lexer<'a>>) -> Result<Term, String> {
    match lex.peek() {
        Some(Token::Var(s)) => {
            let s = s.clone();
            lex.next();
            Ok(Term::Var(s))
        }
        Some(Token::Lambda) => {
            lex.next();
            if let Term::Pi(v, ty, body) = parse_pi(lex)? {
                Ok(Term::Lambda(v, ty, body))
            } else {
                panic!("Unexpected return of `parse_lambda`.")
            }
        }
        Some(Token::Pi) => {
            lex.next();
            parse_pi(lex)
        }
        Some(Token::LParen) => {
            lex.next();
            let t = parse_term(lex);
            if lex.peek() == Some(&Token::RParen) {
                lex.next();
                t
            } else {
                Err(format!("Expected closing parenthesis, got {:?}", lex.peek()).to_string())
            }
        }
        Some(Token::Type) => {
            lex.next();
            Ok(Term::Type(0)) //I need a fresh universe here.
        }
        _ => Err(format!("Unexpected token {:?}", lex.peek()).to_string()),
    }
}

fn parse_pi<'a>(lex: &mut Peekable<Lexer<'a>>) -> Result<Term, String> {
    if let Some(Token::Var(v)) = lex.peek() {
        let v = v.clone();
        lex.next();
        let mut ty = Term::Type(0); // Should be a placeholder, as of now, it is a default.
        if lex.peek() == Some(&Token::Colon) {
            lex.next();
            ty = parse_term(lex)?;
        }
        if lex.peek() == Some(&Token::Comma) {
            lex.next();
            let body = parse_term(lex)?;
            Ok(Term::Pi(v, Rc::new(ty), Box::new(body)))
        } else {
            Err(format!("Expected comma after binder, got {:?}", lex.peek()).to_string())
        }
    } else {
        Err(format!("Expected identifier after 'forall', got {:?}", lex.peek()).to_string())
    }
}

