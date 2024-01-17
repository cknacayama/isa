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
              | primary_expr
              | postfix_expr '(' expr_list? ')'
              | postfix_expr '[' expr ']'
              ;
primary_expr  =
              | '(' expr ')'
              | ident
              | integer
              | float
              | character
              | string
              | array
              | proc_lit
              | 'true'
              | 'false'
              ;

expr_list = expr { ',' expr } ;
array     = '[' expr_list ']' ;
proc_lit  = 'proc' '(' param_list? ')' [ '->' type ] block ;

ident     = / [a-zA-Z_][a-zA-z0-9_]*
integer   = / [0-9][0-9]*
float     = / integer\.integer
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
     | array_sig
     ;

type_list = type { ',' type } ;

array_sig  = '[' type ';' integer ']' ;
proc_sig   = 'proc' '(' type_list? ')' [ '->' type ] ;

```
