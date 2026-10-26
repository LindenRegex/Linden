/* Adapted from RegElk (https://github.com/LindenRegex/RegElk) */

%{
open Raw
%}

%token <char> CHAR
%token <char> NZDIGIT
%token ALT
%token LPAR RPAR
%token LBRAC RBRAC COMMA
%token LBRACK RBRACK
%token STAR PLUS QMARK
%token HAT DOLLAR BACKSL DOT
%token COLONS LESS MORE EQUAL MINUS EXCL
%token LOWB UPB LOWD UPD LOWS UPS LOWW UPW
%token LOWF LOWN LOWR LOWT LOWV LOWK LOWX LOWU LOWP UPP
%token ZERO
%token EOF

%start <Raw.raw_regex> main

%%

decimaldigit:
  | nz=NZDIGIT { nz }
  | ZERO { '0' }

decimaldigits:
  | d1=decimaldigits d2=decimaldigit { d1 ^ String.make 1 d2 }
  | d=decimaldigit { String.make 1 d }


/* https://tc39.es/ecma262/#sec-patterns */

main: r=pattern EOF { r }

pattern:
  | d=disjunction { d }

disjunction:
  | a=alternative { a }
  | a=alternative ALT d=disjunction { Raw_alt(a,d) }

alternative:
  | a=alternative t=term { Raw_con(a,t) }
  | t=term { t } /* differs from the spec here */
  | { Raw_empty }

term:
  | a=assertion { a }
  | a=atom { a }
  | a=atom q=quantifier { Raw_quant(q,a) }

assertion:
  | HAT { Raw_anchor(BeginInput) }
  | DOLLAR { Raw_anchor(EndInput) }
  | BACKSL LOWB { Raw_anchor(WordBoundary) }
  | BACKSL UPB { Raw_anchor(NonWordBoundary) }
  | LPAR QMARK EQUAL d=disjunction RPAR { Raw_lookaround(Lookahead, d) }
  | LPAR QMARK EXCL d=disjunction RPAR { Raw_lookaround(NegLookahead, d) }
  | LPAR QMARK LESS EQUAL d=disjunction RPAR { Raw_lookaround(Lookbehind, d) }
  | LPAR QMARK LESS EXCL d=disjunction RPAR { Raw_lookaround(NegLookbehind, d) }

quantifier:
  | q=quantifierprefix { q }
  | q=quantifierprefix QMARK { {q with greedy=false} }

quantifierprefix:
  | STAR { {min=0; max=None; greedy=true} }
  | PLUS { {min=1; max=None; greedy=true} }
  | QMARK { {min=0; max=Some 1; greedy=true} }
  | LBRAC d=decimaldigits RBRAC { {min=int_of_string d; max=Some (int_of_string d); greedy=true} }
  | LBRAC d=decimaldigits COMMA RBRAC { {min=int_of_string d; max=None; greedy=true} }
  | LBRAC dmin=decimaldigits COMMA dmax=decimaldigits RBRAC { {min=int_of_string dmin; max=Some (int_of_string dmax); greedy=true} }

atom:
  | c=patterncharacter { Raw_character(Char c) }
  | DOT { Raw_character(Dot) }
  | BACKSL a=atomescape { a }
  | c=characterclass { Raw_character c }
  | LPAR d=disjunction RPAR { Raw_capture d }
  | LPAR QMARK COLONS d=disjunction RPAR { d }

syntaxcharacter:
  | HAT { '^' }
  | DOLLAR { '$' }
  | BACKSL { '\\' }
  | DOT { '.' }
  | STAR { '*' }
  | PLUS { '+' }
  | QMARK { '?' }
  | LPAR { '(' }
  | RPAR { ')' }
  | LBRACK { '[' }
  | RBRACK { ']' }
  | LBRAC { '{' }
  | RBRAC { '}' }
  | ALT { '|' }

patterncharacter:
  | c=CHAR { c }
/* also adding all tokens that can be parsed as single characters */
  | LOWB { 'b' }
  | UPB { 'B' }
  | LOWD { 'd' }
  | UPD { 'D' }
  | LOWS { 's' }
  | UPS { 'S' }
  | LOWW { 'w' }
  | UPW { 'W' }
  | LOWF { 'f' }
  | LOWN { 'n' }
  | LOWR { 'r' }
  | LOWT { 't' }
  | LOWV { 'v' }
  | LOWK { 'k' }
  | LOWX { 'x' }
  | LOWU { 'u' }
  | LOWP { 'p' }
  | UPP { 'P' }
  | COMMA { ',' }
  | COLONS { ':' }
  | LESS { '<' }
  | MORE { '>' }
  | EQUAL { '=' }
  | MINUS { '-' }
  | EXCL { '!' }
  | LBRAC { '{' }
  | RBRAC { '}' }
  | LBRACK { '[' }
  | RBRACK { ']' }
  | d=decimaldigit { d }


atomescape:
  | d=decimalescape { Raw_backref (int_of_string d) }
  | c=characterclassescape { Raw_character(Group c) }
  | c=characterescape { Raw_character(Char c) }
  | LOWK { raise (Unsupported "named groups") }

characterescape:
  | c=controlescape { c }
  | ZERO { char_of_int 0 }
  | LOWX { raise (Unsupported "hexadecimal escapes") }
  | LOWU { raise (Unsupported "unicode escapes") }
  | i=identityescape { i }

controlescape:
  | LOWF { '\x0C' }
  | LOWN { '\n' }
  | LOWR { '\r' }
  | LOWT { '\t' }
  | LOWV { char_of_int 11 }

identityescape:
  | s=syntaxcharacter { s }
/* all other characters that represent themselves when escaped */
  | c=CHAR { c }
  | COMMA { ',' }
  | COLONS { ':' }
  | LESS { '<' }
  | MORE { '>' }
  | EQUAL { '=' }
  | MINUS { '-' }
  | EXCL { '!' }

decimalescape:
  | nz=NZDIGIT d=decimaldigits { String.make 1 nz ^ d }
  | nz=NZDIGIT { String.make 1 nz }

characterclassescape:
  | LOWD { Digit }
  | UPD { NonDigit }
  | LOWS { Space }
  | UPS { NonSpace }
  | LOWW { Word }
  | UPW { NonWord }
  | LOWP { raise (Unsupported "unicode properties") }
  | UPP { raise (Unsupported "unicode properties") }

characterclass:
  | LBRACK HAT c=classcontents RBRACK { NegClass c }
  | LBRACK c=classcontents RBRACK { Class c }

classcontents:
  | { [] }
  | n=nonemptyclassranges { n }

nonemptyclassranges:
  | a=classatom { [a] }
  | a=classatom n=nonemptyclassrangesnodash { a::n }
  | a1=classatom MINUS a2=classatom c=classcontents { (make_range a1 a2) @ c }

nonemptyclassrangesnodash:
  | a=classatom { [a] }
  | a=classatomnodash n=nonemptyclassrangesnodash { a::n }
  | a1=classatomnodash MINUS a2=classatom c=classcontents { (make_range a1 a2) @ c }

classatom:
  | MINUS { CChar '-' }
  | c=classatomnodash { c }

classatomnodash:
  | BACKSL c=classescape { c }
  | c=classatomnodashchar { CChar c }

classatomnodashchar:
/* all characters except \, ] and - */
  | HAT { '^' }
  | DOLLAR { '$' }
  | DOT { '.' }
  | STAR { '*' }
  | PLUS { '+' }
  | QMARK { '?' }
  | LPAR { '(' }
  | RPAR { ')' }
  | LBRACK { '[' }
  | LBRAC { '{' }
  | RBRAC { '}' }
  | ALT { '|' }
  | c=CHAR { c }
  | LOWB { 'b' }
  | UPB { 'B' }
  | LOWD { 'd' }
  | UPD { 'D' }
  | LOWS { 's' }
  | UPS { 'S' }
  | LOWW { 'w' }
  | UPW { 'W' }
  | LOWF { 'f' }
  | LOWN { 'n' }
  | LOWR { 'r' }
  | LOWT { 't' }
  | LOWV { 'v' }
  | LOWK { 'k' }
  | LOWX { 'x' }
  | LOWU { 'u' }
  | LOWP { 'p' }
  | UPP { 'P' }
  | COMMA { ',' }
  | COLONS { ':' }
  | LESS { '<' }
  | MORE { '>' }
  | EQUAL { '=' }
  | EXCL { '!' }
  | d=decimaldigit { d }

classescape:
  | LOWB { CChar (char_of_int 8) } /* backspace ascii character */
  | c=characterclassescape { CGroup c }
  | c=characterescape  { CChar c }
  | decimalescape { raise (Unsupported "octal escapes") }


%%
