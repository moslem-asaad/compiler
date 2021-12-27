(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;


let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

  (* run this first! *)
  let annotate_lexical_addresses pe = 
   let rec run pe params env =
      match pe with
      |ScmConst(x) -> ScmConst'(x)
      |ScmVar(var) -> ScmVar'(tag_lexical_address_for_var var params env)
      |ScmIf(test,dit,dif) -> ScmIf'(run test params env, run dit params env,run dif params env)
      |ScmSet(ScmVar(first),second) -> ScmSet'(tag_lexical_address_for_var first params env,run second params env) 
      |ScmDef(ScmVar(first),second) -> ScmDef'(VarFree(first),run second params env)
      |ScmApplic(rator,rand) -> ScmApplic'(run rator params env,List.map (fun expr -> run expr params env) rand)
      |ScmOr(lst) -> ScmOr'(List.map (fun expr -> run expr params env) lst)
      |ScmSeq(lst) -> ScmSeq'(List.map (fun expr -> run expr params env) lst)
      |ScmLambdaSimple(prms,body) -> ScmLambdaSimple'(prms,run body prms (params::env))
      |ScmLambdaOpt(params_list,prm,body) -> ScmLambdaOpt'(params_list,prm,run body (params_list@[prm]) (params::env))
      |_ -> raise X_this_should_not_happen
   in
   run pe [] [];;

  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;
  
  (* run this second! *)
  let annotate_tail_calls pe =
   let rec run pe in_tail = match pe with
      |ScmConst' a  -> pe
      |ScmVar' a -> pe
      |ScmIf'(test,dit,dif) -> ScmIf'(run test false, run dit in_tail, run dif in_tail)
      |ScmSet'(var,pse) -> ScmSet'(var, run pse false)
      |ScmApplic'(rator,rand) -> if(in_tail)
                                 then ScmApplicTP'(run rator false,(List.map (fun exp -> run exp false) rand))
                                 else ScmApplic'(run rator false,(List.map (fun exp -> run exp false) rand))
      |ScmLambdaSimple'(prms,body) -> ScmLambdaSimple'(prms,run body true)
      |ScmLambdaOpt'(params_list,prm,body) -> ScmLambdaOpt'(params_list,prm,run body true)
      |ScmDef'(var,prse) -> ScmDef'(var,run prse false)
      |ScmSeq'(lst) ->ScmSeq'(List.mapi(fun i e -> if (i = (List.length lst) - 1) then run e in_tail else run e false) lst)
      |ScmOr' lst ->ScmOr'(List.mapi(fun i e -> if (i = (List.length lst) - 1) then run e in_tail else run e false) lst)
      | _ -> raise X_this_should_not_happen
   in 
   run pe false;;



    


  (* boxing *)
  let rec get_index_arr num = 
  match num with
  |(-1) -> []
  |0 ->[0]
  |num -> (get_index_arr (num-1))@[num];;

  let rec find_reads name enclosing_lambda expr = match expr,enclosing_lambda with
    |ScmConst'(x),_-> []
    |ScmVar'(VarParam(temp_name ,index)), el when temp_name=name-> [(VarParam(temp_name ,index), el)]
    |ScmVar'(VarBound(temp_name ,index1 , index2)), el when temp_name=name-> [(VarBound(temp_name ,index1 , index2), el)]
    |ScmBox'(var),_ -> []
    |ScmBoxGet'(var),_ -> []
    |ScmBoxSet'(var, val1) , el -> find_reads name el val1
    |ScmIf'(test, dit, dif),el -> (find_reads name el test)@(find_reads name el dit)@(find_reads name el dif)
    |ScmSeq'(lst), el -> (List.fold_right (fun a acc -> acc@(find_reads name el a) ) lst [])
    |ScmOr'(lst), el -> (List.fold_right (fun a acc -> acc@(find_reads name el a) ) lst [])
    |ScmDef'(var, val1),el -> find_reads name el val1
    |ScmSet'(var, val1),el -> find_reads name el val1
    |ScmApplic'(rator, rands),el -> (find_reads name el rator)@(List.fold_right (fun a acc -> acc@(find_reads name el a) ) rands [])
    |ScmApplicTP'(rator, rands),el -> (find_reads name el rator)@(List.fold_right (fun a acc -> acc@(find_reads name el a) ) rands [])
    |ScmLambdaSimple'(var_list,body),None when (List.mem name var_list)=false -> find_reads name (Some(expr)) body 
    |ScmLambdaSimple'(var_list,body),el when (List.mem name var_list)=false -> find_reads name el body 
    |ScmLambdaOpt'(var_list,var_opt,body),None when (List.mem name (var_opt::var_list))=false -> find_reads name (Some(expr)) body
    |ScmLambdaOpt'(var_list,var_opt,body),el when (List.mem name (var_opt::var_list))=false -> find_reads name el body 
    |_,_ -> [];;

  let rec find_sets name enclosing_lambda expr = match expr,enclosing_lambda with
    |ScmConst'(x),_-> []
    |ScmVar'(var),_ -> []
    |ScmBox'(var),_ -> []
    |ScmBoxGet'(var),_ -> []
    |ScmBoxSet'(var,val1),el -> find_sets name el val1
    |ScmIf'(test, dit, dif),el -> (find_sets name el test)@(find_sets name el dit)@(find_sets name el dif)
    |ScmSeq'(lst), el -> (List.fold_right (fun a acc -> acc@(find_sets name el a) ) lst [])
    |ScmOr'(lst), el -> (List.fold_right (fun a acc -> acc@(find_sets name el a) ) lst [])
    |ScmDef'(var, val1),el -> find_sets name el val1
    |ScmApplic'(rator, rands),el -> (find_sets name el rator)@(List.fold_right (fun a acc -> acc@(find_sets name el a) ) rands [])
    |ScmApplicTP'(rator, rands),el -> (find_sets name el rator)@(List.fold_right (fun a acc -> acc@(find_sets name el a) ) rands [])
    |ScmLambdaSimple'(var_list,body),None when (List.mem name var_list)=false -> find_sets name (Some(expr)) body 
    |ScmLambdaSimple'(var_list,body),el when (List.mem name var_list)=false -> find_sets name el body 
    |ScmLambdaOpt'(var_list,var_opt,body),None when (List.mem name (var_opt::var_list))=false -> find_sets name (Some(expr)) body
    |ScmLambdaOpt'(var_list,var_opt,body),el when (List.mem name (var_opt::var_list))=false -> find_sets name el body 
    |ScmSet'(VarParam(temp_name ,index), val1),el when temp_name=name -> [(VarParam(temp_name ,index), el)]
    |ScmSet'(VarParam(temp_name ,index), val1),el -> find_sets name el val1
    |ScmSet'(VarBound(temp_name ,index1 , index2), val1),el when temp_name=name -> [(VarBound(temp_name ,index1 , index2), el)]
    |ScmSet'(VarBound(temp_name ,index1 , index2), val1),el -> find_sets name el val1
    |_,_ -> [];;


  let is_valid_read_write a b =
  match a,b with
  |(VarParam(temp_name1 ,index1),el1) , (VarParam(temp_name2 ,index2),el2) -> false
  |(VarParam(temp_name1 ,index),el1), (VarBound(temp_name2 ,index1 , index2),el2) -> true
  |(VarBound(temp_name1 ,index1 , index2),el1) , (VarParam(temp_name2 ,index),el2) -> true
  |(VarBound(temp_name1 ,idx1 , idx2),Some(el1)) , (VarBound(temp_name2 ,index1 , index2),Some(el2)) -> ((el1==el2)=false);;


  let rec must_replace_var lst1 lst2 = 
    match lst1,lst2 with
    |[],[]-> false
    |[],a::arr -> false
    |a::arr,[] -> false
    |a::arr , arr2 -> (List.fold_right (fun elem acc -> acc||(is_valid_read_write a elem) ) arr2 false) || (must_replace_var arr arr2);;

  let rec replace_var varName body = match body with
  |ScmConst'(a) -> body
  |ScmBox'(var) -> body
  |ScmBoxGet'(var) -> body
  |ScmBoxSet'(var, val1) -> ScmBoxSet'(var, replace_var varName val1)
  |ScmIf'(test, dit, dif) -> ScmIf'(replace_var varName test, replace_var varName dit, replace_var varName dif)
  |ScmSeq'(lst)-> ScmSeq'(List.map (fun a -> replace_var varName a) lst)
  |ScmOr'(lst)-> ScmOr'(List.map (fun a -> replace_var varName a) lst)
  |ScmDef'(var, val1) -> ScmDef'(var, replace_var varName val1)
  |ScmLambdaSimple'(var_list , lambdaBody) when (List.mem varName var_list)=false -> ScmLambdaSimple'(var_list ,replace_var varName lambdaBody)
  |ScmLambdaSimple'(var_list , lambdaBody) -> ScmLambdaSimple'(var_list ,lambdaBody)
  |ScmLambdaOpt'(var_list,var_opt,lambdaBody) when (List.mem varName (var_opt::var_list))=false -> ScmLambdaOpt'(var_list,var_opt,replace_var varName lambdaBody)
  |ScmLambdaOpt'(var_list,var_opt,lambdaBody) -> ScmLambdaOpt'(var_list,var_opt,lambdaBody)
  |ScmApplic'(rator , rands) -> ScmApplic'(replace_var varName rator ,(List.map (fun arg -> replace_var varName arg) rands))
  |ScmApplicTP'(rator , rands) -> ScmApplicTP'(replace_var varName rator ,(List.map (fun arg -> replace_var varName arg) rands))
  |ScmVar'(VarParam(param_name, index)) when param_name=varName -> ScmBoxGet'(VarParam(param_name, index))
  |ScmVar'(VarBound(param_name, index1 , index2)) when param_name=varName -> ScmBoxGet'(VarBound(param_name, index1 , index2))
  |ScmVar'(var)-> body
  |ScmSet'(VarParam(param_name, index) , val1) when param_name=varName -> ScmBoxSet'(VarParam(param_name, index) , replace_var varName val1)
  |ScmSet'(VarBound(param_name, index1 , index2) , val1) when param_name=varName -> ScmBoxSet'(VarBound(param_name, index1 , index2) , replace_var varName val1)
  |ScmSet'(var , val1) -> ScmSet'(var , replace_var varName val1);;


  let setVarToBox param_name index exp = match exp with
    |ScmSeq'(lst) -> ScmSeq'( (ScmSet'(VarParam(param_name, index), ScmBox'(VarParam(param_name, index)))) ::lst)
    |expr -> ScmSeq'((ScmSet'(VarParam(param_name, index), ScmBox'(VarParam(param_name, index))))::[expr]);;

  let set_lambda_body varName index body = 
    if(must_replace_var (find_reads varName None body) (find_sets varName None body))
    then (setVarToBox varName index (replace_var varName body))
    else body;;
      


  let rec box_set expr = 
    match expr with
    |ScmConst' a -> expr
    |ScmVar' a -> expr
    |ScmIf'(test,dit,dif) -> ScmIf'(box_set test,box_set dit, box_set dif)
    |ScmSet'(var,val1) -> ScmSet'(var, box_set val1)
    |ScmApplic'(rator,rand) -> ScmApplic'(box_set rator,(List.map (fun arg1 ->box_set arg1) rand))
    |ScmApplicTP'(rator,rand) -> ScmApplicTP'(box_set rator,(List.map (fun arg1 ->box_set arg1) rand))
    |ScmDef'(var,val1) -> ScmDef'(var,box_set val1)
    |ScmSeq'(lst) -> ScmSeq'(List.map (fun arg1 ->box_set arg1) lst)
    |ScmOr'(lst) -> ScmOr'(List.map (fun arg1 ->box_set arg1) lst)
    |ScmLambdaSimple'(var_list, body) -> ScmLambdaSimple'(var_list,(List.fold_right2 set_lambda_body var_list (get_index_arr ((List.length var_list)-1)) (box_set body) ))
    |ScmLambdaOpt'(var_list,var_opt, body) -> ScmLambdaOpt'(var_list, var_opt, (List.fold_right2 set_lambda_body (var_list@[var_opt]) (get_index_arr ((List.length (var_list@[var_opt]))-1)) (box_set body)))
    |_-> expr;;
  


  let run_semantics expr =
       box_set (annotate_tail_calls
            (annotate_lexical_addresses expr));;

end;; (* end of module Semantic_Analysis *)


(*aaaaaaaa*)
