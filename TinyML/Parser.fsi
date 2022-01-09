// Signature file for parser generated by fsyacc
module TinyML.Parser
type token = 
  | EOF
  | IF
  | THEN
  | ELSE
  | FUN
  | ARROW
  | LET
  | REC
  | IN
  | TRUE
  | FALSE
  | BRA
  | KET
  | PLUS
  | MINUS
  | STAR
  | SLASH
  | PERCENT
  | LT
  | GT
  | LEQ
  | GEQ
  | EQ
  | NEQ
  | AND
  | OR
  | NOT
  | COLON
  | SEMICOLON2
  | COMMA
  | SEQUENCE
  | STRING of (System.String)
  | ID of (System.String)
  | CHAR of (System.Char)
  | FLOAT of (System.Double)
  | INT of (System.Int32)
type tokenId = 
    | TOKEN_EOF
    | TOKEN_IF
    | TOKEN_THEN
    | TOKEN_ELSE
    | TOKEN_FUN
    | TOKEN_ARROW
    | TOKEN_LET
    | TOKEN_REC
    | TOKEN_IN
    | TOKEN_TRUE
    | TOKEN_FALSE
    | TOKEN_BRA
    | TOKEN_KET
    | TOKEN_PLUS
    | TOKEN_MINUS
    | TOKEN_STAR
    | TOKEN_SLASH
    | TOKEN_PERCENT
    | TOKEN_LT
    | TOKEN_GT
    | TOKEN_LEQ
    | TOKEN_GEQ
    | TOKEN_EQ
    | TOKEN_NEQ
    | TOKEN_AND
    | TOKEN_OR
    | TOKEN_NOT
    | TOKEN_COLON
    | TOKEN_SEMICOLON2
    | TOKEN_COMMA
    | TOKEN_SEQUENCE
    | TOKEN_STRING
    | TOKEN_ID
    | TOKEN_CHAR
    | TOKEN_FLOAT
    | TOKEN_INT
    | TOKEN_end_of_input
    | TOKEN_error
type nonTerminalId = 
    | NONTERM__startinteractive
    | NONTERM__startprogram
    | NONTERM_program
    | NONTERM_interactive
    | NONTERM_expr
    | NONTERM_binding
    | NONTERM_expr_app_atom
    | NONTERM_expr_tuple_atom
    | NONTERM_expr_tuple_atoms
    | NONTERM_ty
    | NONTERM_ty_tuple
    | NONTERM_tuple_decompose_id
    | NONTERM_tuple_decompose_id_list
    | NONTERM_tuple_decompose_ids
/// This function maps tokens to integer indexes
val tagOfToken: token -> int

/// This function maps integer indexes to symbolic token ids
val tokenTagToTokenId: int -> tokenId

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
val prodIdxToNonTerminal: int -> nonTerminalId

/// This function gets the name of a token as a string
val token_to_string: token -> string
val interactive : (FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> FSharp.Text.Lexing.LexBuffer<'cty> -> ( TinyML.Ast.interactive ) 
val program : (FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> FSharp.Text.Lexing.LexBuffer<'cty> -> ( TinyML.Ast.expr ) 
