/*
 *  The scanner definition for COOL.
 */

/*
 *  Stuff enclosed in %{ %} in the first section is copied verbatim to the
 *  output, so headers and global definitions are placed here to be visible
 * to the code in the file.  Don't remove anything that was here initially
 */
%{
#include <cool-parse.h>
#include <stringtab.h>
#include <utilities.h>

/* The compiler assumes these identifiers. */
#define yylval cool_yylval
#define yylex  cool_yylex

/* Max size of string constants */
#define MAX_STR_CONST 1025
#define YY_NO_UNPUT   /* keep g++ happy */

extern FILE *fin; /* we read from this file */

/* define YY_INPUT so we read from the FILE fin:
 * This change makes it possible to use this scanner in
 * the Cool compiler.
 */
#undef YY_INPUT
#define YY_INPUT(buf,result,max_size) \
	if ( (result = fread( (char*)buf, sizeof(char), max_size, fin)) < 0) \
		YY_FATAL_ERROR( "read() in flex scanner failed");

char string_buf[MAX_STR_CONST]; /* to assemble string constants */
char *string_buf_ptr;

extern int curr_lineno;
extern int verbose_flag;

extern YYSTYPE cool_yylval;

/*
 *  Add Your own definitions here
 */

static int comment_layer = 0;

%}

/*
 * Define names for regular expressions here.
 */

CLASS           ?i:class
ELSE            ?i:else
FI              ?i:fi
IF              ?i:if
IN              ?i:in
INHERITS        ?i:inherits
LET             ?i:let
LOOP            ?i:loop
POOL            ?i:pool
THEN            ?i:then
WHILE           ?i:while
CASE            ?i:case
ESAC            ?i:esac
OF              ?i:of
DARROW          =>
NEW             ?i:new
ISVOID          ?i:isvoid
ASSIGN          <-
NOT             ?i:not
LE              <= 

WHITE_SPACE     [ \t\r\f\v]
VALID_CHAR      [+/\-\*=<.~,;:()@{}]
INVALID         [^a-zA-Z0-9{WHITE_SPACE}{VALID_CHAR}]

OBJECT          [a-z]+[a-zA-Z0-9_]*
TYPE            [A-Z]+[a-zA-Z0-9_]*
INT             [0-9]+

%x COMMENT
%x INLINE_COMMENT
%x STRING
%x ERROR_STRING

%%

 /*
  *  Nested comments
  */

"(*"                    { BEGIN(COMMENT); comment_layer++; }
<COMMENT>"(*"           { comment_layer++; }
<COMMENT>"*)"           { comment_layer--; if(comment_layer == 0) BEGIN(INITIAL); }
<COMMENT>[^*\n(]*        { 
                          /* 
                            eat anything not * \n  (
                          */
                        }
<COMMENT>[*()]          {}
<COMMENT>"\n"           { curr_lineno++; }
"*)"                    { cool_yylval.error_msg = "Unmatched *)"; return (ERROR);}
<COMMENT><<EOF>>        { BEGIN(INITIAL); cool_yylval.error_msg = "EOF in comment"; return (ERROR);}

"--"                    { BEGIN(INLINE_COMMENT); }
<INLINE_COMMENT>.*       { }
<INLINE_COMMENT>\n       { BEGIN(INITIAL); curr_lineno++; }
<INLINE_COMMENT><<EOF>>  { BEGIN(INITIAL); }


 /*
  *  The multiple-character operators.
  */
{DARROW}		{ return (DARROW); }
{ASSIGN}		{ return (ASSIGN); }
{LE}        { return (LE); }

 /*
  * Keywords are case-insensitive except for the values true and false,
  * which must begin with a lower-case letter.
  */
{CLASS}		{ return (CLASS); }
{ELSE}			{ return (ELSE); }
{FI}			{ return (FI); }
{IF}			{ return (IF); }
{IN}			{ return (IN); }
{INHERITS}		{ return (INHERITS); }
{LET}			{ return (LET); }
{LOOP}			{ return (LOOP); }
{POOL}			{ return (POOL); }
{THEN}			{ return (THEN); }
{WHILE}			{ return (WHILE); }
{CASE}			{ return (CASE); }
{ESAC}			{ return (ESAC); }
{OF}			{ return (OF); }

{NEW}			{ return (NEW); }
{ISVOID}		{ return (ISVOID); }

{NOT}      { return (NOT); }


 /*
  *  String constants (C syntax)
  *  Escape sequence \c is accepted for all characters c. Except for 
  *  \n \t \b \f, the result is c.
  *
  */
\n              {curr_lineno++;}
{WHITE_SPACE}   {}
{VALID_CHAR}    {return (char) yytext[0];}


t(?i:rue)            {cool_yylval.boolean = true; return (BOOL_CONST);}
f(?i:alse)           {cool_yylval.boolean = false; return (BOOL_CONST);}
{OBJECT}        {cool_yylval.symbol = stringtable.add_string(yytext); return (OBJECTID);}
{TYPE}          {cool_yylval.symbol = stringtable.add_string(yytext); return (TYPEID);}
{INT}           {cool_yylval.symbol = inttable.add_string(yytext); return (INT_CONST);}

\"                { BEGIN(STRING); string_buf_ptr = string_buf; }
<STRING>\"        { 
                      BEGIN(INITIAL);
                      *string_buf_ptr = '\0'; 
                      if(string_buf_ptr >= string_buf + MAX_STR_CONST) {
                        cool_yylval.error_msg = "String constant too long";
                        return (ERROR);
                      }
                      cool_yylval.symbol = stringtable.add_string(string_buf); 
                      return (STR_CONST);
                  }
<ERROR_STRING>\"               { 
                                  BEGIN(INITIAL); 
                                  cool_yylval.error_msg = "String contains null character"; 
                                  return (ERROR);
                                }
<STRING,ERROR_STRING>\n        { BEGIN(INITIAL); cool_yylval.error_msg = "Unterminated string constant"; return (ERROR);}
<STRING,ERROR_STRING><<EOF>>   { BEGIN(INITIAL); cool_yylval.error_msg = "EOF in string constant"; return (ERROR);} 
<STRING,ERROR_STRING>\0        { BEGIN(ERROR_STRING);}        
<STRING,ERROR_STRING>\\n       { *string_buf_ptr++ = '\n';}
<STRING,ERROR_STRING>\\t       { *string_buf_ptr++ = '\t';}
<STRING,ERROR_STRING>\\f       { *string_buf_ptr++ = '\f';}
<STRING,ERROR_STRING>\\b       { *string_buf_ptr++ = '\b';}
<STRING,ERROR_STRING>\\0       { *string_buf_ptr++ = '0';}
<STRING,ERROR_STRING>\\\"      { *string_buf_ptr++ = '\"';}
<STRING,ERROR_STRING>\\        { *string_buf_ptr++ = '\\';}
<STRING,ERROR_STRING>\\[^\0]     { *string_buf_ptr++ = yytext[1];}
<STRING,ERROR_STRING>[^\"\n\\\0]+  {
                    char* yyptr = yytext;
                    while(*yyptr) {
                      *string_buf_ptr++ = *yyptr++;
                    }
                  }

  /*
  *  left character is error
  */
[^\n]       {cool_yylval.error_msg = yytext; return (ERROR);}
%%
