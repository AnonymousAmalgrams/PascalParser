%{     /* pars1.y    Pascal Parser      Gordon S. Novak Jr.  ; 30 Jul 13   */

/* Copyright (c) 2013 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/* 14 Feb 01; 01 Oct 04; 02 Mar 07; 27 Feb 08; 24 Jul 09; 02 Aug 12 */

/*
; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, see <http://www.gnu.org/licenses/>.
  */


/* NOTE:   Copy your lexan.l lexical analyzer to this directory.      */

       /* To use:
                     make pars1y              has 1 shift/reduce conflict
                     pars1y                   execute the parser
                     i:=j .
                     ^D                       control-D to end input

                     pars1y                   execute the parser
                     begin i:=j; if i+j then x:=a+b*c else x:=a*b+c; k:=i end.
                     ^D

                     pars1y                   execute the parser
                     if x+y then if y+z then i:=j else k:=2.
                     ^D

           You may copy pars1.y to be parse.y and extend it for your
           assignment.  Then use   make parser   as above.
        */

        /* Yacc reports 1 shift/reduce conflict, due to the ELSE part of
           the IF statement, but Yacc's default resolves it in the right way.*/

#include <string.h>
#include <stdio.h>
#include <ctype.h>
#include "token.h"
#include "lexan.h"
#include "symtab.h"
#include "parse.h"


        /* define the type of the Yacc stack element to be TOKEN */

#define YYSTYPE TOKEN

TOKEN parseresult;

%}

/* Order of tokens corresponds to tokendefs.c; do not change */

%token IDENTIFIER STRING NUMBER   /* token types */

%token PLUS MINUS TIMES DIVIDE    /* Operators */
%token ASSIGN EQ NE LT LE GE GT POINT DOT AND OR NOT DIV MOD IN

%token COMMA                      /* Delimiters */
%token SEMICOLON COLON LPAREN RPAREN LBRACKET RBRACKET DOTDOT

%token ARRAY BEGINBEGIN           /* Lex uses BEGIN */
%token CASE CONST DO DOWNTO ELSE END FILEFILE FOR FUNCTION GOTO IF LABEL NIL
%token OF PACKED PROCEDURE PROGRAM RECORD REPEAT SET THEN TO TYPE UNTIL
%token VAR WHILE WITH
%left  PLUS MINUS OR
%left  TIMES DIVIDE DIV MOD AND
%right UMINUS UPLUS

%%

  program    :  statement DOT                  { parseresult = $1; }
             ;
  statement  :  BEGINBEGIN statement endpart
                                       { $$ = makeprogn($1,cons($2, $3)); }
             |  IF expr THEN statement endif   { $$ = makeif($1, $2, $4, $5); }
             |  FOR assignment TO expr DO statement	{ $$ = makefor(1, $1, $2, $3, $4, $5, $6); }
             |  FOR assignment DOWNTO expr DO statement	{ $$ = makefor(-1, $1, $2, $3, $4, $5, $6); }
             |  assignment
             ;
  endpart    :  SEMICOLON statement endpart    { $$ = cons($2, $3); }
             |  END                            { $$ = NULL; }
             ;
  endif      :  ELSE statement                 { $$ = $2; }
             |  /* empty */                    { $$ = NULL; }
             ;
  assignment :  IDENTIFIER ASSIGN expr         { $$ = binop($2, $1, $3); }
             ;
  expr       : expr compare_op simple_expr     { $$ = binop($2, $1, $3); }
             | simple_expr
			 ;
  simple_expr :  simple_expr plus_op term      { $$ = binop($2, $1, $3); }
              |  MINUS term %prec UMINUS       { $$ = unaryop($1, $2); }
              |  PLUS term %prec UPLUS         { $$ = unaryop($1, $2); }
			  |  term 
              ;
  term       :  term times_op factor           { $$ = binop($2, $1, $3); }
             |  factor
             ;
  factor     :  LPAREN expr RPAREN             { $$ = $2; }
             |  unsigned_constant
             ;
  plus_op    :  PLUS
  	  	     |  MINUS
			 |  OR
			 ;
  times_op   :  TIMES
  	  	  	 |  DIVIDE
			 |  DIV
			 |  MOD
			 |  AND
			 ;
  compare_op :  EQ 
             |  LT 
			 |  GT 
			 |  NE 
			 |  LE 
			 |  GE 
			 |  IN
			 ;
  unsigned_constant : IDENTIFIER 
                    | NUMBER 
					| NIL 
					| STRING
					;
  sign       : PLUS 
             | MINUS
			 ;

%%

/* You should add your own debugging flags below, and add debugging
   printouts to your programs.

   You will want to change DEBUG to turn off printouts once things
   are working.
  */

#define DEBUG        63             /* set bits here for debugging, 0 = off  */
#define DB_CONS       1             /* bit to trace cons */
#define DB_BINOP      2             /* bit to trace binop */
#define DB_MAKEIF     4             /* bit to trace makeif */
#define DB_MAKEPROGN  8             /* bit to trace makeprogn */
#define DB_PARSERES  16             /* bit to trace parseresult */
#define DB_UNARYOP   32             /* bit to trace unaryop */
 int labelnumber = 0;  /* sequential counter for internal label numbers */

   /*  Note: you should add to the above values and insert debugging
       printouts in your routines similar to those that are shown here.     */

TOKEN cons(TOKEN item, TOKEN list)           /* add item to front of list */
  { item->link = list;
    if (DEBUG & DB_CONS)
       { printf("cons\n");
         dbugprinttok(item);
         dbugprinttok(list);
       };
    return item;
  }

TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs)        /* reduce binary operator */
  { op->operands = lhs;          /* link operands to operator       */
    lhs->link = rhs;             /* link second operand to first    */
    rhs->link = NULL;            /* terminate operand list          */
    if (DEBUG & DB_BINOP)
       { printf("binop\n");
         dbugprinttok(op);
         dbugprinttok(lhs);
         dbugprinttok(rhs);
       };
    return op;
  }

/* unaryop links a unary operator op to one operand, lhs */
TOKEN unaryop(TOKEN op, TOKEN lhs) {
	op->operands = lhs;          /* link operands to operator       */
	lhs->link = NULL;             /* terminate operand list    */
	if (DEBUG & DB_UNARYOP) { 
		printf("unaryop\n");
	    dbugprinttok(op);
	    dbugprinttok(lhs);
	};
	return op;
}

/* makeop makes a new operator token with operator number opnum.
   Example:  makeop(FLOATOP)  */
TOKEN makeop(int opnum) {
	TOKEN tok = talloc();
	tok->tokentype = OPERATOR;
	tok->whichval = opnum;
	return tok;
}

TOKEN makeif(TOKEN tok, TOKEN exp, TOKEN thenpart, TOKEN elsepart)
  {  tok->tokentype = OPERATOR;  /* Make it look like an operator   */
     tok->whichval = IFOP;
     if (elsepart != NULL) elsepart->link = NULL;
     thenpart->link = elsepart;
     exp->link = thenpart;
     tok->operands = exp;
     if (DEBUG & DB_MAKEIF)
        { printf("makeif\n");
          dbugprinttok(tok);
          dbugprinttok(exp);
          dbugprinttok(thenpart);
          dbugprinttok(elsepart);
        };
     return tok;
   }

TOKEN makeprogn(TOKEN tok, TOKEN statements)
  {  tok->tokentype = OPERATOR;
     tok->whichval = PROGNOP;
     tok->operands = statements;
     if (DEBUG & DB_MAKEPROGN)
       { printf("makeprogn\n");
         dbugprinttok(tok);
         dbugprinttok(statements);
       };
     return tok;
   }

/* fillintc smashes tok, making it into an INTEGER constant with value num */
TOKEN fillintc(TOKEN tok, int num) {
	tok->tokentype = NUMBERTOK;
	tok->intval = num;
	tok->datatype = INTEGER;
	return tok;
}

/* makeintc makes a new token with num as its value */
TOKEN makeintc(int num) {
	TOKEN tok = talloc();
	fillintc(tok, num);
	return tok;
}

/* makelabel makes a new label, using labelnumber++ */
TOKEN makelabel() {
	TOKEN label = makeop(LABELOP);
	TOKEN labelnum = makeintc(labelnumber);
	labelnumber++;
	return unaryop(label, labelnum);
}

/* makegoto makes a GOTO operator to go to the specified label.
   The label number is put into a number token. */
TOKEN makegoto(int label) {
	TOKEN goto_tok = makeop(GOTOOP);
	TOKEN labelnum = makeintc(label);
	return unaryop(goto_tok, labelnum);
}

/* copytok makes a new token that is a copy of origtok */
TOKEN copytok(TOKEN origtok) {
	TOKEN tok = talloc();
	memcpy(tok, origtok, sizeof(struct tokn));
	return tok;
}

/* makefor makes structures for a for statement.
   sign is 1 for normal loop, -1 for downto.
   asg is an assignment statement, e.g. (:= i 1)
   endexpr is the end expression
   tok, tokb and tokc are (now) unused tokens that are recycled. */
TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr,
              TOKEN tokc, TOKEN statement) {
	int cur_labelnumber = labelnumber;
	TOKEN label_tok = makelabel();
	TOKEN goto_tok = makegoto(cur_labelnumber);
	TOKEN assign_var = copytok(asg->operands);
	TOKEN assign_var1 = copytok(asg->operands);
	TOKEN assign_var2 = copytok(asg->operands);
	TOKEN end_check_tok = 0;
	TOKEN tok_increment = 0;
	TOKEN tok_var_incr = 0;
	if (sign == 1) {
	   //(<= i endpart) 
		end_check_tok = makeop(LEOP);
		tok_increment = makeop(PLUSOP);
	} else {
		//(>= i endpart) 
		end_check_tok = makeop(GEOP);
		tok_increment = makeop(MINUSOP);
	}
	end_check_tok = binop(end_check_tok, assign_var, endexpr);
	fillintc(tokb, 1);
	binop(tok_increment, assign_var1, tokb);
	tok_var_incr = makeop(ASSIGNOP);
	binop(tok_var_incr, assign_var2, tok_increment);
	cons(statement, cons(tok_var_incr, goto_tok));
	makeprogn(tokc, statement);
	tok = makeif(tok, end_check_tok, tokc, 0);
	cons(label_tok, tok);
	cons(asg, label_tok); 
	return makeprogn(talloc(), asg);
	
	
}

int wordaddress(int n, int wordsize)
  { return ((n + wordsize - 1) / wordsize) * wordsize; }
 
yyerror(s)
  char * s;
  { 
  fputs(s,stderr); putc('\n',stderr);
  }

main()
  { int res;
    initsyms();
    res = yyparse();
    printst();
    printf("yyparse result = %8d\n", res);
    if (DEBUG & DB_PARSERES) dbugprinttok(parseresult);
    ppexpr(parseresult);           /* Pretty-print the result tree */
  }
