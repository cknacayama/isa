```
program = decl_list? ;

decl_list = decl+ ;
decl      = proc_decl ;

proc_decl   = 'proc' ident '(' param_list? ')' [ '->' type ] block ;

param_list = param { ',' param } ;
param      = ident ':' type ;

block     = '{' stmt_list? '}' ;
stmt_list = stmt+ ;

stmt =
     | let_decl
     | proc_decl
     | ret_stmt
     | if_stmt
     | while_stmt
     | block
     | expr_stmt
     ;

let_decl   = 'let' 'mut'? ident [ ':' type ] [ '=' expr ] ';' ;
ret_stmt   = 'return' expr? ';' ;
if_stmt    = 'if' expr block [ 'else' ( if_stmt | block ) ] ;
while_stmt = 'while' expr block ;
expr_stmt  = expr? ';' ;

expr          = assign_expr ;
assign_expr   = bool_or_expr [ '=' assign_expr ] ;
bool_or_expr  = bool_and_expr { '||' bool_and_expr } ;
bool_and_expr = bit_or_expr { '&&' bit_or_expr } ;
bit_or_expr   = bit_xor_expr { '|' bit_xor_expr } ;
bit_xor_expr  = bit_and_expr { '^' bit_and_expr } ;
bit_and_expr  = eq_expr { '&' eq_expr } ;
eq_expr       = rel_expr { ( '==' | '!=' ) rel_expr } ;
rel_expr      = shift_expr { ( '>' | '>=' | '<' | '<=' ) shift_expr } ;
shift_expr    = add_expr { ( '>>' | '<<' ) add_expr } ;
add_expr      = mul_expr { ( '+' | '-' ) mul_expr } ;
mul_expr      = un_expr { ( '*' | '/' | '%' ) un_expr } ;
un_expr       = 
              | ( '!' | '-' | '~' | type ) un_expr
              | postfix_expr
              ;
postfix_expr  =
              | ident '(' arg_list? ')'
              | primary_expr
              ;
primary_expr  =
              | '(' expr ')'
              | ident
              | integer
              | float
              | character
              | string
              | 'true'
              | 'false'
              ;

ident     = / [a-zA-Z_][a-zA-z0-9_]*
integer   = / [0-9][0-9]*
character = / '(.|\\[nrt0"'])'
string    = / "[^"]*"

type = 
     | 'unit'
     | 'bool'
     | 'char'
     | 'int'
     | 'float'
     | 'string'
     | proc_sig
     ;

type_list = type { ',' type } ;

proc_sig   = 'proc' '(' type_list? ')' [ '->' type ] ;

```
