#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with 
|ScmNil -> ScmConst(ScmNil)
|ScmBoolean(x) -> ScmConst(ScmBoolean(x))
|ScmChar(x) -> ScmConst(ScmChar(x))
|ScmString(x) -> ScmConst(ScmString(x))
|ScmNumber(x) -> ScmConst(ScmNumber(x))
|ScmPair(ScmSymbol "quote",ScmPair(x,ScmNil)) -> ScmConst(x)
|ScmSymbol(x) -> if (List.mem x reserved_word_list)
                  then raise(X_reserved_word x)
                  else ScmVar(x)
|ScmPair(ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmNil))) -> 
  ScmIf(tag_parse_expression(test), tag_parse_expression(dit), ScmConst(ScmVoid))
|ScmPair (ScmSymbol "if",ScmPair(test, ScmPair (dit, ScmPair (dif, ScmNil)))) -> 
  ScmIf(tag_parse_expression(test), tag_parse_expression(dit), tag_parse_expression(dif))
|ScmPair (ScmSymbol "or", ScmNil) -> ScmConst (ScmBoolean(false))
|ScmPair(ScmSymbol "or",ScmPair(x,ScmNil)) -> tag_parse_expression(x)
|ScmPair(ScmSymbol "or",rest) when (scm_is_list rest)-> ScmOr(List.map tag_parse_expression (scm_list_to_list rest))
|ScmPair(ScmSymbol "lambda",ScmPair(args,rest)) when (scm_is_list args) && (scm_is_list rest) && rest != ScmNil-> ScmLambdaSimple((List.map handle_lambda_simple_arg (scm_list_to_list args)), (handle_lambda_body rest))
|ScmPair(ScmSymbol "lambda",ScmPair(ScmSymbol var,rest)) when (scm_is_list rest) && rest != ScmNil-> ScmLambdaOpt([],var,(handle_lambda_body rest))
|ScmPair(ScmSymbol "lambda",ScmPair(ScmPair(ScmSymbol first,sec),rest)) when (scm_is_list rest) && rest != ScmNil -> ScmLambdaOpt([first]@(handle_lambda_opt_args sec),(handle_lambda_opt_single_arg sec),(handle_lambda_body rest))
|ScmPair(ScmSymbol "define",ScmPair(ScmSymbol x,ScmPair(y,ScmNil))) -> if (List.mem x reserved_word_list)
                                                                        then raise(X_reserved_word x)
                                                                        else ScmDef(ScmVar(x), tag_parse_expression(y))
|ScmPair(ScmSymbol "define",ScmPair(ScmPair(ScmSymbol x,args),rest)) -> ScmDef(ScmVar(x), tag_parse_expression(ScmPair(ScmSymbol "lambda" , ScmPair(args,rest))))
|ScmPair(ScmSymbol "set!",ScmPair(ScmSymbol x,ScmPair(y,ScmNil))) -> ScmSet(ScmVar(x),tag_parse_expression(y))                                                                 
|ScmPair(ScmSymbol "begin",rest) when (scm_is_list rest)-> ScmSeq (List.map tag_parse_expression (scm_list_to_list rest))
|ScmPair(x,rest) when (scm_is_list rest)-> ScmApplic(tag_parse_expression(x), (List.map tag_parse_expression (scm_list_to_list rest)))


| _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))

and handle_lambda_opt_args args = 
match args with
|ScmPair (ScmSymbol x, rest) -> [x]@(handle_lambda_opt_args rest)
|ScmSymbol x -> []
|_ -> raise X_not_implemented

and handle_lambda_opt_single_arg args = 
match args with
|ScmPair (ScmSymbol x, rest) -> handle_lambda_opt_single_arg(rest)
|ScmSymbol x -> x
|_ -> raise X_not_implemented

and handle_lambda_body body = 
match body with
|ScmPair (x, ScmNil) -> tag_parse_expression(x)
|body -> tag_parse_expression(ScmPair(ScmSymbol "begin",body))

and handle_lambda_simple_arg x = 
match x with 
|ScmSymbol(var) -> if (List.mem var reserved_word_list)
                  then raise(X_reserved_word var)
                  else var
|_ -> raise X_not_implemented

and macro_expand sexpr =
match sexpr with
|ScmPair (ScmSymbol "and", ScmNil) -> ScmBoolean(true)
|ScmPair(ScmSymbol "and",ScmPair(x,ScmNil)) -> x
|ScmPair (ScmSymbol "and", ScmPair(x,rest)) -> ScmPair(ScmSymbol "if" ,ScmPair(x,ScmPair(macro_expand(ScmPair(ScmSymbol("and"),rest)),ScmPair(ScmBoolean(false),ScmNil))))
|ScmPair(ScmSymbol "let",ScmPair(args, rest)) when (scm_is_list args)-> ScmPair(ScmPair(ScmSymbol "lambda" , ScmPair(list_to_proper_list (List.map let_pairArgs_to_args (scm_list_to_list args)),rest)),list_to_proper_list((List.map let_pairArgs_to_Exp (scm_list_to_list args))))
|ScmPair(ScmSymbol "let*", ScmPair(first,rest)) when (scm_is_list first) && (scm_list_length first)<2 -> macro_expand(ScmPair(ScmSymbol "let", ScmPair(first,rest)))
|ScmPair(ScmSymbol "let*", ScmPair(ScmPair(first,last),rest)) when (scm_is_list (ScmPair(first,last))) -> macro_expand(ScmPair(ScmSymbol "let", ScmPair(ScmPair(first,ScmNil),ScmPair(macro_expand(ScmPair(ScmSymbol "let*" ,ScmPair(last,rest))),ScmNil))))
| ScmPair(ScmSymbol("letrec"), ScmPair(args, body)) -> macro_expand (handle_let_rec args body)
|ScmPair(ScmSymbol "cond" , ScmPair(ScmPair(first,last),ScmNil)) when (scm_is_list last)-> macro_expand(ScmPair(                          ScmSymbol("if")    ,       ScmPair(                                  first,             ScmPair(ScmPair(ScmSymbol("begin"),last) , ScmNil)                         )                       ))
|ScmPair(ScmSymbol "cond" , ScmPair(ScmPair(first,last),rest)) when (scm_is_list last) -> macro_expand(ScmPair(ScmSymbol("if") , ScmPair(first,ScmPair(ScmPair(ScmSymbol("begin"),last),macro_expand(ScmPair(ScmSymbol("cond"),rest))))))
| _ -> sexpr

and handle_let_rec args body = 
match args with 
|ScmNil ->ScmPair(ScmSymbol "let",ScmPair(ScmNil,body))
|ScmPair(first,rest) -> ScmPair(ScmSymbol"let",ScmPair(handle_args args,make_set args body))

and handle_args args =
match args with
|ScmPair(ScmPair(arg,ScmPair(vl,ScmNil)),ScmNil) ->ScmPair(ScmPair(arg,ScmPair(ScmPair(ScmSymbol "quote",ScmPair(ScmSymbol "whatever",ScmNil)),ScmNil)),ScmNil)
|ScmPair(ScmPair(arg,ScmPair(vl,ScmNil)),rest) ->ScmPair(ScmPair(arg,ScmPair(ScmPair(ScmSymbol "quote",ScmPair(ScmSymbol "whatever",ScmNil)),ScmNil)),handle_args rest)
 
and make_set args body = 
match args with
|ScmPair(ScmPair(arg,ScmPair(vl,ScmNil)),ScmNil) ->ScmPair(ScmPair(ScmSymbol "set!",ScmPair(arg,ScmPair(vl,ScmNil))),body)
|ScmPair(ScmPair(arg,ScmPair(vl,ScmNil)),rest) -> ScmPair(ScmPair(ScmSymbol "set!",ScmPair(arg,ScmPair(vl,ScmNil))),make_set rest body)

and let_pairArgs_to_args args = 
match args with
| ScmPair(ScmSymbol x ,rest) when (scm_is_list rest) -> ScmSymbol(x)
| _ -> raise X_not_implemented

and let_pairArgs_to_Exp args = 
match args with
| ScmPair(ScmSymbol x ,ScmPair(y,rest)) when (scm_is_list rest) -> y
| _ -> raise X_not_implemented



end;; 



(* |ScmPair(ScmSymbol "cond" , ScmPair(ScmPair(first,ScmPair(ScmSymbol("=>"),last)),rest)) when (scm_is_list last) -> 
|ScmPair(ScmSymbol "cond" , ScmPair(ScmPair(ScmSymbol("=>"))) *)

