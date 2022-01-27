#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string

end;;



module Code_Gen : CODE_GEN = struct
(*constant table*)

let rec remove_dups lst = 
  match lst with
  |[] -> []
  |hd::tl -> hd::(remove_dups(List.filter(fun e -> not (e = hd)) tl));;

let init_table = [ScmVoid;ScmNil;ScmBoolean false;ScmBoolean true];;

let rec gather_consts asts = 
  match asts with
  |ScmConst'(x) -> [x]
  |ScmBoxSet'(var,express) -> gather_consts express
  |ScmIf'(test,dit,dif) -> (gather_consts test)@(gather_consts dit)@(gather_consts dif)
  |ScmSeq'(lst) -> List.flatten(List.map gather_consts lst)
  |ScmSet'(var,express) -> gather_consts express
  |ScmDef'(var,express) -> gather_consts express
  |ScmOr'(lst)-> List.flatten(List.map gather_consts lst)
  |ScmLambdaSimple'(strlst,express) -> gather_consts express
  |ScmLambdaOpt'(strlst,str,express)-> gather_consts express
  |ScmApplic'(express,exprlst) -> handle_Applic_kinds express exprlst
  |ScmApplicTP'(express,exprlst) -> handle_Applic_kinds express exprlst
  |_ -> []

and handle_Applic_kinds op exprlst = 
  let maplst = (List.map gather_consts ([op]@exprlst)) in
  let result = List.flatten maplst in
  result

and make_expantion const_lst =
  match const_lst with
  |ScmSymbol(s) -> [ScmString s;const_lst]
  |ScmPair(car,cdr)-> make_expantion(car)@make_expantion(cdr)@[car;cdr;const_lst]
  |ScmVector(v) -> (expand_vector v)@[const_lst] 
  | _ -> [const_lst]

and expand_vector v = 
  match v with 
  |hd::[] -> make_expantion hd 
  |hd::tl -> (make_expantion hd)@(expand_vector tl)
  | _ -> []

and make_gathered_ast_as_one_lst ast = 
  let const_tbl_lsts = List.map gather_consts ast in
  let compined_lsts = List.flatten const_tbl_lsts in 
  compined_lsts

and build_first_table asts = 
  let const_tbl_lst = make_gathered_ast_as_one_lst asts in 
  let completed_init_tbl = init_table@const_tbl_lst in 
  let removed_dups_lst = remove_dups completed_init_tbl in
  let expanded_lst_step1 = List.map make_expantion removed_dups_lst in 
  let expanded_lst_step2 = List.flatten expanded_lst_step1 in
  let final_lst = remove_dups expanded_lst_step2 in 
  final_lst
  
and create_table const_table offset const_lst =
  match const_lst with
  |[] -> const_table
  |hd::tl -> (match hd with
              |ScmVoid -> create_table (const_table@[(ScmVoid,(offset,"db T_VOID"))]) (offset+1) tl
              |ScmNil -> create_table (const_table@[(hd,(offset,"db T_NIL"))]) (offset+1) tl
              |ScmBoolean(false) -> create_table (const_table@[(hd,(offset,"db T_BOOL, 0"))]) (offset+2) tl
              |ScmBoolean(true) -> create_table (const_table@[(hd,(offset,"db T_BOOL, 1"))]) (offset+2) tl
              |ScmNumber(ScmRational(x1,x2)) -> create_table (const_table@[(hd,(offset,"MAKE_LITERAL_RATIONAL("^(string_of_int (x1))^","^(string_of_int (x2))^")"))]) (offset+17) tl
              |ScmNumber(ScmReal x) -> create_table (const_table@[(hd,(offset,"MAKE_LITERAL_FLOAT("^(string_of_float(x))^")"))]) (offset+9) tl
              |ScmChar c -> create_table (const_table@[(hd,(offset,"MAKE_LITERAL_CHAR("^(string_of_int (int_of_char (c)))^")"))]) (offset+2) tl
              |ScmSymbol s-> create_table (const_table@(handle_symbol s offset const_table)) (offset+9) tl
              |ScmString str -> create_table (const_table@[(hd,(offset,"MAKE_LITERAL_STRING \""^str^"\""))]) (offset+9+(String.length str)) tl
              |ScmPair(car,cdr) -> create_table (const_table@(handle_pair car cdr offset const_table)) (offset+17) tl
              |ScmVector(lst) -> handle_vector lst offset const_table tl
              )

and handle_symbol s offset const_table = 
  let lst = [(ScmSymbol s,(offset,"MAKE_LITERAL_SYMBOL(const_tbl+"^(string_of_int (find_offset (ScmString s) const_table))^")"))] in
  lst

and handle_pair car cdr offset const_table = 
  let lst = [(ScmPair(car,cdr),(offset,"MAKE_LITERAL_PAIR(const_tbl+"^(string_of_int(find_offset car const_table))^", const_tbl+"^(string_of_int(find_offset cdr const_table))^")"))] in 
  lst 

and find_offset e table = fst (List.assoc e table)

and handle_vector lst offset table tl =
  let offsets_size = find_vector_offsets lst table in
  let str_vector = cast_vector_elements lst table in 
  create_table (table@[(ScmVector(lst),(offset,str_vector))]) (offset+offsets_size) tl
  
and find_vector_offsets lst table = 
  if (List.length lst = 0) then 1
  else 9+8*(List.length lst)

and cast_vector_elements lst table = 
  if(List.length lst = 0) then "MAKE_LITERAL_VECTOR"
  else(
      let str = List.fold_left(fun acc curr -> acc ^" const_tbl+"^(string_of_int (find_offset (curr) table))^",") "" lst in
      let sub_str = String.sub str 0 ((String.length str) -1) in 
      "MAKE_LITERAL_VECTOR"^ sub_str);;

(* free var table*)

let init_free_vars = [(* Type queries  *)
                      "boolean?"; "flonum?"; "rational?";
                      "pair?"; "null?"; "char?"; "string?";
                      "procedure?"; "symbol?";
                      (* String procedures *)
                      "string-length"; "string-ref"; "string-set!";
                      "make-string"; "symbol->string";
                      (* Type conversions *)
                      "char->integer"; "integer->char"; "exact->inexact";
                      (* Identity test *)
                      "eq?";
                      (* Arithmetic ops *)
                      "+"; "*"; "/"; "="; "<";
                      (* Additional rational numebr ops *)
                      "numerator"; "denominator"; "gcd";
                      (* List ops *)
                      "apply";"car"; "cdr"; "cons"; "set-car!"; "set-cdr!";
                      (*stdlib funcs*)   
                      "map"; "fold-left"; "fold-right"; "cons*"; "append"; "list"; "list?";
                      "not"; "-"; ">"; "gcd"; "zero?"; "integer?"; "number?"; "length"; "string->list"; "equal?";   
                     ]

let rec find_free_vars asts = 
  match asts with
  |ScmVar'(VarFree s) -> [s]
  |ScmBox'(VarFree s) -> [s]
  |ScmBoxGet'(VarFree s) -> [s]
  |ScmBoxSet'(v,e) -> (check_free_var v) @ (find_free_vars e)
  |ScmIf'(test,dit,dif) ->(find_free_vars test) @ (find_free_vars dit) @(find_free_vars dif)
  |ScmSeq'(lst) -> List.flatten(List.map find_free_vars lst)
  |ScmSet'(v,e) -> (check_free_var v) @(find_free_vars e)
  |ScmDef'(v,e) -> (check_free_var v)@(find_free_vars e)
  |ScmOr'(lst) -> List.flatten(List.map find_free_vars lst)
  |ScmLambdaSimple'(_,body) ->find_free_vars body 
  |ScmLambdaOpt'(args,arg,body) -> find_free_vars body 
  |ScmApplic'(e,lst) -> (find_free_vars e) @ (List.flatten(List.map find_free_vars lst))
  |ScmApplicTP'(e,lst) -> (find_free_vars e) @ (List.flatten(List.map find_free_vars lst))
  |_ -> []
  
and check_free_var v = 
  match v with  
  |VarFree s -> [s]
  |_ -> []

and offset_mul_8 table = 
match table with
|(car,offset)::[] -> [(car,offset*8)]
|(car,offset)::cdr -> [(car,offset*8)]@(offset_mul_8 cdr)
| _ -> []

and create_vf_table asts = 
  let free_vars = List.flatten(List.map find_free_vars asts) in 
  let compined_free_vars = init_free_vars@free_vars in 
  let final_free_vars = remove_dups compined_free_vars in 
  let table = List.mapi(fun index var -> (var,index)) final_free_vars in
  let mul_8_tbl = offset_mul_8 table in
  mul_8_tbl;;

(*generate*)
let counter = ref 0;;
let set_and_get = (fun() -> let old_count = !counter in counter:=(!counter+1) ; old_count);;

  let rec start_generating const_table fv_table expr size = 
  match expr with
  |ScmConst'(c) -> "mov rax, const_tbl + "^(string_of_int (find_offset c const_table))^"\n"
  |ScmDef' (VarFree(v),e) -> let address = find_fv_index v fv_table in
                               (start_generating const_table fv_table e size)^"\n"^
                               "mov qword [fvar_tbl + " ^ (string_of_int address) ^ "], rax\n" ^
                               "mov rax, SOB_VOID_ADDRESS\n"
  |ScmVar'(VarParam(_,minor)) -> "mov rax, qword[rbp + 8 *(4 + "^(string_of_int minor)^")]\n"
  |ScmSet'(VarParam(_,minor),e) -> start_generating const_table fv_table e size ^ "\n mov qword[rbp+8*(4+"^(string_of_int minor)^")],rax\n"
                                  ^"mov rax, SOB_VOID_ADDRESS\n"
  |ScmVar'(VarBound(_,major,minor)) -> "mov rax, qword [rbp + 8 * 2]\n"^
                                       "mov rax, qword [rax + 8 * "^(string_of_int major)^"]\n"^
                                       "mov rax, qword [rax + 8 * "^(string_of_int minor)^"]\n"
  |ScmSet'(VarBound(_,major,minor),e) -> start_generating const_table fv_table e size ^
                                         "\nmov rbx, qword [rbp + 8 * 2]\n"^
                                         "mov rbx, qword [rbx + 8 * "^(string_of_int major)^"]\n"^
                                         "mov qword [rbx + 8 * "^(string_of_int minor)^"], rax\n"^
                                         "mov rax, SOB_VOID_ADDRESS\n"
  |ScmVar'(VarFree(v)) -> let address = find_fv_index v fv_table in 
                          "mov rax, qword[fvar_tbl + "^(string_of_int address)^"]\n" 
  |ScmSet'(VarFree(v),e) -> let address = find_fv_index v fv_table in
                            start_generating const_table fv_table e size ^
                            "\nmov qword [fvar_tbl + "^(string_of_int address)^"],rax\n"^
                            "mov rax, SOB_VOID_ADDRESS\n"
  |ScmSeq'(lst) -> List.fold_left (fun acc curr -> acc ^ (start_generating const_table fv_table curr size)) "" lst
  |ScmOr'(lst) -> generate_or lst const_table fv_table size
  |ScmIf'(test,dit,dif) -> generate_if test dit dif const_table fv_table size
  |ScmBox'(var) -> start_generating const_table fv_table (ScmVar'(var)) size ^
                   "\nMALLOC r8, WORD_SIZE\n"^
                   "mov qword[r8], rax\n"^
                   "mov rax, r8\n"
  |ScmBoxGet'(var) -> start_generating const_table fv_table (ScmVar'(var)) size ^
                      "\nmov rax, qword [rax]\n"
                      
  |ScmBoxSet'(var,e) -> start_generating const_table fv_table e size ^
                        "\npush rax\n"^
                        start_generating const_table fv_table (ScmVar'(var)) size ^
                        "\npop qword [rax]\n"^ 
                        "mov rax, SOB_VOID_ADDRESS\n"
                        
  |ScmLambdaSimple'(args,body) -> let index = string_of_int (set_and_get()) in
                                  let lcont_label = "Lcont" ^ index in
                                  let lcode_label = "Lcode" ^ index in
                                  let enviroment = handle_env lcont_label lcode_label size index in
                                  let lcode_code = generate_Lcode const_table fv_table body (size+1) in
                                  ";LambdaSimple\n"^
                                  enviroment^"\n"^
                                  lcode_label ^ ":\n" ^ lcode_code ^ lcont_label ^":\n"
                                   
  |ScmApplic'(proc,args) -> let args_code = List.fold_right (fun arg acc -> acc^(start_generating const_table fv_table arg size)^"\npush rax\n") args " " in
                            let proc_code = start_generating const_table fv_table proc size in
                            ";Applic\n"^ 
                            args_code^"push "^(string_of_int(List.length args))^"\n"^proc_code^"\n"^
                            (*Verify that rax has type closure ??? *)
                            "CLOSURE_ENV r10, rax\n"^
                            "push r10 ; push rax -> env\n"^
                            "CLOSURE_CODE r10, rax\n"^
                            "call r10 ; call rax ->code\n"^
                            "add rsp, 8 * 1\n"^
                            "pop rbx\n"^
                            "lea rsp, [rsp + 8 * rbx]\n"
                        
  |ScmApplicTP'(proc,args) -> let args_code = List.fold_right (fun arg acc -> acc^(start_generating const_table fv_table arg size)^"\npush rax\n") args " " in
                            let proc_code = start_generating const_table fv_table proc size in 
                            let frame_size = string_of_int(List.length args + 4) in
                            ";ApplicTP\n"^
                            args_code^"push "^(string_of_int(List.length args))^"\n"^proc_code^"\n"^
                            (*Verify that rax has type closure ??? *)
                            "CLOSURE_ENV r10, rax\n"^
                            "push r10 ; push rax -> env\n"^
                            "push qword [rbp + 8 * 1]\n"^
                            "push qword [rbp]\n"^
                            "mov r10, qword[rbp + 8 * 3] ; old args number"^"\n"^
                            "add r10 ,4\n"^
                            "shl r10, 3  ; old frame size"^"\n"^
                            "SHIFT_FRAME "^frame_size^"\n"^
                            "add rsp, r10\n"^
                            "pop rbp\n"^
                            "CLOSURE_CODE r10, rax\n"^
                            "jmp r10\n"
      
    |ScmLambdaOpt'(args,oparg,body) -> let index = string_of_int (set_and_get()) in
                                       let lcont_label = "Lcont" ^ index in
                                       let lcode_label = "Lcode" ^ index in
                                       let enviroment = handle_env lcont_label lcode_label size index in
                                       let lcode_code = generate_Lcode_opt const_table fv_table (size+1) args oparg body index in
                                       ";LambdaOpt\n"^ 
                                       enviroment^"\n"^lcode_label^":\n"^lcode_code^lcont_label^":\n"
    | _ -> ""

and generate_or lst const_table fv_table size = 
  let lexit_label = "Lexit" ^(string_of_int (set_and_get())) in
  let rec gen_or_help str lst =
  match lst with
  |[] -> ""
  |hd::[] -> str ^ start_generating const_table fv_table hd size ^lexit_label^":\n"
  |hd::tl -> gen_or_help (str^start_generating const_table fv_table hd size ^
                          "\ncmp rax, SOB_FALSE_ADDRESS\n"^
                          "jne "^lexit_label^"\n"
                          ) tl in 
  gen_or_help "" lst 

and generate_if test dit dif const_table fv_table size = 
    let lelse_label = "Lelse"^(string_of_int (set_and_get())) in 
    let lexit_label = "Lexit"^(string_of_int (set_and_get())) in 
    let test_gen = start_generating const_table fv_table test size in 
    let test_gen_block = test_gen^
                         "\ncmp rax, SOB_FALSE_ADDRESS\nje "^lelse_label^"\n" in 
    let dit_gen = start_generating const_table fv_table dit size in
    let dit_gen_block = dit_gen^
                        "\njmp "^lexit_label^"\n" in 
    let dif_gen = start_generating const_table fv_table dif size in
    let dif_gen_block = lelse_label^":\n"^dif_gen^"\n"^lexit_label^":\n" in
    let result = test_gen_block^dit_gen_block^dif_gen_block in 
    result

and handle_env lcont_label lcode_label size index =
    let make_closure_label = "make_closure"^index in
    let copy_loop_label = "copy_loop"^ index in 
    let end_copy_loop_label = "end_copy_loop"^index in
    let copy_params_label = "copy_params"^index in
    let end_copy_param_loop_label = "end_copy_param_loop"^index in
    (*allocate the ExtEnv code*)
    "MALLOC rbx, 8 * "^(string_of_int (size+1)) ^ " ; rbx is apoiner the the extended enviroment\n"^
    (*Copy pointers of minor vectors from Env (on the stack) to ExtEnv (with offset of1)*)
    "xor rcx, rcx ;rcx = 0\n"^
    "mov rdx, "^(string_of_int size)^"\n"^
    copy_loop_label^":\n"^
    "cmp rcx, rdx\n"^
    "je "^end_copy_loop_label^"\n"^
    "mov r8, [rbp + 8 * 2]\n"^
    "mov r9, qword[r8 + 8 * rcx]\n"^
    "mov qword[rbx + 8 * (rcx + 1)], r9\n"^
    "inc rcx\n"^
    "jmp "^copy_loop_label^"\n"^
    end_copy_loop_label^":\n"^
    (*Allocate ExtEnv[0] to point to a vector where to store the parameters*)
    "mov r15, qword[rbp + 8 * 3] ; |argc|\n"^
    "shl r15, 3\n"^
    "MALLOC rdx, r15\n"^
    (* Copy the parameters off of the stack *)
    "mov rcx, qword[rbp + 8 * 3]\n"^
    "cmp rcx, 0\n"^
    "je "^make_closure_label^"\n"^
    "xor rcx, rcx\n"^
    copy_params_label^":\n"^
    "mov r12, qword[rbp + 8 * 3]\n"^
    "cmp rcx, r12\n"^
    "je "^end_copy_param_loop_label^"\n"^
    "mov r15, PVAR(rcx)       ;r15 = Param_i\n"^
    "mov qword [rdx + 8*(rcx)], r15     ;ExtEnv [0][i] = Param_i\n"^
    "inc rcx\n"^
    "jmp "^copy_params_label^"\n"^
    end_copy_param_loop_label^":\n"^
    "mov qword[rbx], rdx\n"^
    (* Allocate the closure object; Address in rax *)
    make_closure_label^":\n"^
    "MAKE_CLOSURE(rax, rbx, "^lcode_label^")\n"^
    "jmp "^lcont_label^"\n"

and generate_Lcode const_table fv_table body size = 
    "push rbp\n"^
    "mov rbp, rsp\n"^
    start_generating const_table fv_table body size ^"\n"^
    "leave\n"^
    "ret\n"

and generate_Lcode_opt const_table fv_table size args oparg body index =
    let handle_no_opt_args_label = "handle_no_opt_args"^index in
    let make_list_label = "make_list"^index in
    let shift_frame_label = "shift_frame"^ index in
    let loop_shift_up = "loop_shift_up"^index in
    let end_fix_stack = "end_fix_stack"^index in  
    let loop_shift_down = "loop_shift_down"^index in
    let finish_loop_shift_down = "finish_loop_shift_down"^index in 
    let fix_stack_final = generate_Lcode const_table fv_table body size in
    "mov r13, qword[rsp + 8 * 2] ;r13 = num of all args\n"^
    "mov r14, "^(string_of_int (List.length args))^"  ;;  r14 = num of none opt args\n"^
    "mov rcx, r13\n"^
    "sub rcx, r14 ; rcx = num of opt args\n"^
    "cmp rcx, 0\n"^
    "je "^handle_no_opt_args_label^" ;if there is no opt args then handle this case else handle opt args case\n"^
    "mov r12, SOB_NIL_ADDRESS ;we want to make the list\n"^
    make_list_label^":\n"^
    "mov r11, r14 ; r11 = |args|\n"^
    "add r11, rcx ; r11 = |args + optargs|\n"^
    "mov r10, [rsp + 8 * (2 + r11)]\n"^
    "MAKE_PAIR(rax, r10, r12)\n"^
    "mov r12, rax\n"^
    "dec rcx\n"^
    "cmp rcx, 0\n"^
    "je "^shift_frame_label^"\n"^
    "jmp "^make_list_label^"\n"^
    shift_frame_label^":  ; now we have the list (3 5 8) from the lecture example stored in r12\n"^
    "; now we want to do 2 things : 1- make the top of the frame the list (3 5 8), 2 - change |arg| value to 4(the example)\n"^
    "mov rcx, r13\n"^
    "add rcx, 2 ;|arg| + env + ret\n"^
    "mov qword[rsp + 8 * rcx], r12 ; now the top of the frame is the list\n"^
    "mov rcx ,r14\n"^
    "inc rcx\n"^
    "mov [rsp + 8 * 2], rcx ; |arg| = num of args + 1\n"^
    "inc rcx\n"^
    "inc rcx\n"^
    "mov rdx, r13\n"^
    "inc rdx\n"^
    loop_shift_up^":\n"^
    "dec rcx\n"^
    "mov r9, qword[rsp + 8 * rcx]\n"^
    "mov [rsp + 8 * rdx], r9\n"^
    "dec rdx\n"^
    "cmp rcx, 0\n"^
    "jne "^loop_shift_up^"\n"^
    "mov rcx, r13\n"^
    "sub rcx, r14 ; rcx = num of opt args\n"^
    "dec rcx\n"^
    "shl rcx, 3\n"^
    "add rsp, rcx\n ; rsp points to ret address after shifting the fram\n"^
    "jmp "^end_fix_stack^"\n"^
    handle_no_opt_args_label^":\n"^
    "sub rsp, 8\n"^
    "mov rcx, r13\n"^
    "inc rcx\ninc rcx\n"^
    "mov rdx, 0\n"^
    loop_shift_down^":\n"^
    "mov r9, qword[rsp + 8 * (rdx + 1)]\n"^
    "mov [rsp + 8 * rdx], r9\n"^
    "cmp rdx, rcx\n"^
    "je "^finish_loop_shift_down^"\n"^
    "inc rdx\n"^
    "jmp "^loop_shift_down^"\n"^
    finish_loop_shift_down^":\n"^
    "mov r12, SOB_NIL_ADDRESS ;we want to add the empty list\n"^
    "mov [rsp + 8 * (rdx + 1)], r12\n"^
    "mov [rsp + 8 * rdx], r9\n"^
    "mov rcx, r13\n"^
    "inc rcx\n"^
    "mov [rsp + 8 * 2], rcx ;update |arg|\n"^
    end_fix_stack^":\n"^fix_stack_final
     

and find_fv_index v fv_table = 
  match fv_table with 
  |hd::tl -> (match hd with
              |(var,index) -> if var = v then index else find_fv_index v tl
              |_ -> raise X_this_should_not_happen
              )
  | _ -> raise X_this_should_not_happen ;;

(*------------------END--------------------*)

let make_consts_tbl asts = (*raise X_not_yet_implemented;;*)
  create_table [] 0 (build_first_table asts);;
let make_fvars_tbl asts =(* raise X_not_yet_implemented;;*)
  create_vf_table asts;;
let generate consts fvars e = (*raise X_not_yet_implemented;;*)
  start_generating consts fvars e 0;;
end;;
