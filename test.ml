#use "pc.ml";;
open PC;;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

  let unitify nt = pack nt (fun _ -> ());;


  let nt_whitespace str =
    const (fun ch -> ch <= ' ') str ;;
  

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;






let  nt_boolean str =     
  let tr = word_ci "#t" in 
  let fls = word_ci "#f" in 
  let tr = pack tr (fun _ -> true) in 
  let fls = pack fls (fun _ -> false) in 
  let res = disj tr fls in
  let res = pack res (fun b -> ScmBoolean b ) in
  res str  ;; 

let nt_int str = 
  let dig = range '0' '9' in 
  let nautural = plus dig in
  let nautural = pack nautural (fun (dgt) ->int_of_string (list_to_string dgt)) in
  let pos = char '+' in 
  let neg = char '-' in 
  let pos_or_neg = disj pos neg in
  let nt1 = maybe pos_or_neg in 
  let res = pack (caten nt1 nautural)
            (fun (sign,num)->
              match sign with 
              |None-> num
              |Some('+') -> num
              |Some('-') -> (-1)*num
            ) in
  res str ;; 

let nt_frac str =
  let dig = range '0' '9' in 
  let natural = plus dig in 
  let natural = pack natural (fun (dgt) ->int_of_string (list_to_string dgt)) in
  let nt1 = nt_int in 
  let slash = char '/' in 
  let res = pack (caten (caten nt1 slash) natural) 
            (fun ((num,sl),nat)-> 
            match nat with
            |0 -> ScmSymbol (string_of_int num ^ "/" ^ "0")
            |nat -> ScmNumber(ScmRational (num/(gcd num nat),nat/(gcd num nat)))
            ) in
  res str ;;

let nt_integer_part str = 
  let dig = range '0' '9' in 
  let nt1 = plus dig in
  let nt1 = pack nt1 (fun (dgt) ->int_of_string (list_to_string dgt)) in
  nt1 str ;;

let nt_exponent str =
  let exptoken = disj_list[word "e" ; word "E" ; word "*10^" ; word "*10**"] in 
  let res = caten exptoken nt_int in
  let res = pack res (fun (tok , num) -> num) in 
  res str ;;

let nt_mantissa str = 
  let dig = range '0' '9' in 
  let nt1 = plus dig in 
  let nt1 = pack nt1 (fun (dgt) ->int_of_string (list_to_string dgt)) in
  nt1 str ;;

let nt_floatA str = 
  let nt1 = nt_integer_part in
  let dot = char '.' in 
  let nt1 = caten nt1 dot in 
  let nt1 = pack nt1 (fun (n,d) -> string_of_int n ^ ".") in 
  let nt2 = nt_mantissa in 
  let nt2 = maybe nt2 in 
  let nt1 = caten nt1 nt2 in 
  let nt1 = pack nt1 (fun (num , mntsa) -> 
                      match mntsa with 
                      | None ->  num
                      | Some(m) -> num ^ (string_of_int m ^ "e")  
                     ) in 
  let nt3 = nt_exponent in 
  let nt3 = maybe nt3 in 
  let nt1 = caten nt1 nt3 in 
  let nt1 = pack nt1 (fun (num,exp) -> 
                      match exp with
                      | None -> float_of_string (num ^"0")
                      | Some(e) -> float_of_string (num ^ (string_of_int e))
                     ) in
  nt1 str ;;

let nt_floatB str = 
  let nt1 = char '.' in 
  let nt2 = nt_mantissa in 
  let nt2 = caten nt1 nt2 in 
  let nt2 = pack nt2 (fun (dot,nm) -> "0" ^ "." ^ (string_of_int nm) ^ "e") in 
  let nt1 = maybe nt_exponent in 
  let nt1 = caten nt2 nt1 in 
  let nt1 = pack nt1 (fun (num,exp) -> 
                      match exp with 
                      | None -> float_of_string (num ^"0")
                      | Some(e) -> float_of_string (num ^ (string_of_int e)) 
                     ) in
  nt1 str;;

let nt_floatC str = 
  let nt1 = nt_integer_part  in 
  let nt2 = nt_exponent in 
  let nt1 = pack nt1(fun num -> num ) in 
  let nt2 = pack nt2 (fun num -> num) in 
  let nt3 = caten nt1 nt2 in 
  let res = pack nt3 (fun (n1,n2)-> 
                      match n2 with
                      | 0 ->  float_of_int n1
                      |n2 -> float_of_int n1*.(10. ** float_of_int n2) 
                     ) in
  res str ;;


let nt_float str =
  let pos = char '+' in 
  let neg = char '-' in 
  let pos_neg = disj pos neg in 
  let pos_neg = maybe pos_neg in
  let nt1 = nt_floatA in
  let nt1 = caten pos_neg nt1 in  
  let nt1 = pack nt1 (fun (sign,n) -> 
                       match sign with 
                       | None -> ScmNumber (ScmReal (n))
                       | Some('+') -> ScmNumber (ScmReal (n))
                       | Some('-') -> ScmNumber(ScmReal (-1.0 *. n))
                     ) in
  
  let nt2 = nt_floatB in 
  let nt2 = caten pos_neg nt2 in 
  let nt2 = pack nt2 (fun (sign , n) -> 
                      match sign with 
                      | None -> ScmNumber(ScmReal (n))
                      | Some('+') -> ScmNumber(ScmReal (n))
                      | Some('-') -> ScmNumber(ScmReal (-1.0 *. n))
                     ) in
  let nt1 = disj nt1 nt2 in 
  let nt2 = nt_floatC in 
  let nt2 = caten pos_neg nt2 in 
  let nt2 = pack nt2 (fun (sign , n) -> 
                      match sign with 
                      | None -> ScmNumber(ScmReal (n))
                      | Some('+') ->ScmNumber (ScmReal (n))
                      | Some('-') -> ScmNumber(ScmReal (-1.0 *. n))
                     ) in
  let nt1 = disj nt1 nt2 in 
  nt1 str;;

let nt_char_simple str =
  let nt1 = range '!' '~' in
  let nt1 = not_followed_by nt1 (range '!' '~') in
  let nt1 = pack nt1 (fun c-> c ) in 
  nt1 str;;

let make_named_char char_name ch =
  let nt1 = word char_name in 
  let nt1 = pack nt1 (fun _ -> ch) in
  nt1;;

let  nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "newline" '\n');
               (make_named_char "page" '\012');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "tab" '\t')] in
  nt1 str;;

let make_nt_hex c1 c2 = 
  let nt1 = word_ci "x" in 
  let nt2 = range '0' '9' in 
  let nt2 = pack nt2 (let d = int_of_char '0' in 
                  fun c -> (int_of_char c) - d) in 
  let nt3 = range c1 c2 in 
  let nt3 = pack nt3 (let d =int_of_char c1 - 10 in 
                  fun c -> (int_of_char c) - d) in 
  let nt2 = disj nt2 nt3 in 
  let nt2 = plus nt2 in 
  let nt2 = not_followed_by nt2 (range_ci 'a' 'f') in 
  let nt2 = pack nt2 
            (fun dig -> List.fold_left
                        (fun a b -> 16*a +b)
                        0 
                        dig            
            ) in 
  let nt1 = caten nt1 nt2 in 
  let nt1 = pack nt1 (fun (_ , num)-> num) in 
  nt1;;

let nt_char_hex str =
  let nt1 = disj (make_nt_hex 'a' 'f') (make_nt_hex 'A' 'F') in 
  let nt1 = pack nt1 (fun (c) -> ScmChar (char_of_int c)) in
  nt1 str ;;

let nt_char str = 
    let pref = word "#\\" in 
    let pref = unitify pref in  
    let nt2 = nt_char_simple in
    let nt2 = pack nt2 (fun (c) -> ScmChar (c)) in
    let nt1 = nt_char_named in
    let nt1 = pack nt1 (fun c -> ScmChar (c)) in  
    let nt1 = disj nt1 nt2 in 
    let nt2 = nt_char_hex in 
    let nt1 = disj nt1 nt2 in
    let nt1 = caten pref nt1 in 
    let nt1 = pack nt1 (fun (_,b) -> b) in 
    nt1 str;;

    let nt_symbol_char str = 
      let nt1 = disj_list [(range '0' '9') ; (range 'a' 'z') ; (range 'A' 'Z');
                           (char '!') ; (char '$') ; (char '^') ; (char '*') ;
                           (char '-') ; (char '_') ; (char '=') ; (char '+') ; 
                           (char '<') ; (char '>') ; (char '?') ; (char '/') ; 
                           (char ':');
                          ] in 
      nt1 str;;

let nt_number str =
  let nt1 = nt_float in
  let nt2 = nt_frac in
  let nt3 = pack nt_int (fun n -> ScmNumber(ScmRational(n, 1))) in
  let nt1 = disj nt1 (disj nt2 nt3) in
  (**let nt1 = pack nt1 (fun r -> ScmNumber r) in *)
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str;;
   

   
let nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  let nt1 = diff nt1 nt_number in
  nt1 str ;;



let nt_end_of_line_or_file str =
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str;;

let nt_line_comment str = 
  let nt1 = char ';' in 
  let nt2 = nt_end_of_line_or_file in 
  let nt3 = diff nt_any nt2 in 
  let nt3 = star nt3 in 
  let nt1 = caten nt1(caten nt3 nt2) in 
  let nt1 = unitify nt1 in
  nt1 str;; 

let nt_paired_comment str = 
  let nt1 = char '{' in
  let nt2 = char '}' in 
  let nt3 = diff nt_any nt2 in 
  let nt3 = star nt3 in 
  let nt1 = caten nt1(caten nt3 nt2) in 
  let nt1 = unitify nt1 in
  nt1 str ;; 

let nt_sexpr_comment str = 
  let nt1 = word "#;" in 
  let nt1 = plus nt1 in 
  let nts = nt_symbol in 
  let nt1 = caten nt1 nts in 
  let nt1 = pack nt1 (fun _ -> ()) in 
  nt1 str;;


let nt_comment str =
  disj_list
    [nt_line_comment;
     nt_paired_comment;
     nt_sexpr_comment] str;;

     let nt_skip_star str =
      let nt1 = disj (unitify nt_whitespace) nt_comment in
      let nt1 = unitify (star nt1) in
      nt1 str;;
      
    let make_skipped_star (nt : 'a parser) =
        let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
        let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
        nt1;;



        let nt_sexpr str =
          let nt1 =
          disj_list [nt_number; nt_boolean; nt_char; nt_symbol] in
          let nt1 = make_skipped_star nt1 in
                nt1 str;;

let proper_list lst =
  List.fold_right(fun a b -> ScmPair(a,b)) lst ScmNil;;
   
let nt_proper_list str = 
  let nt1 = char '(' in 
  let nt2 = star nt_sexpr in
  let nt1 = caten nt1 nt2 in
  let nt2 = char ')' in 
  let nt1 = caten nt1 nt2 in 
  let nt1 = pack nt1 (fun ((_,lst),_)->
                      List.fold_right 
                      (fun a b -> ScmPair(a,b))
                      lst ScmNil) in
  nt1 str ;;
  
let nt_improper_list str = 
  let nt1 = char '(' in 
  let nt2 = plus nt_sexpr in 
  let nt1 = caten nt1 nt2 in
  let dt = char '.' in
  let nt1 = caten nt1 dt in
  let nt1 = caten nt1 nt_sexpr in
  let nt1 = caten nt1 (char ')') in
  let nt1 = pack nt1 (fun ((((_,l),d),x),_)-> 
                      List.fold_right 
                      (fun a b -> (ScmPair (a,b))) l x
                     ) in
  
 
  nt1 str ;;
  
let nt_list str = 
    let nt1 = star nt_proper_list in
    let nt2 = star nt_improper_list in
    let nt1 = disj nt1 nt2 in
    nt1 str;;


  
let nt_quoted str = 
  let nt1 = char '\x27' in
  let nt1 = plus nt1 in 
  let nt2 = nt_sexpr in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (a,b)->
                      List.fold_right
                      (fun x y ->(ScmPair (ScmSymbol "quote",(ScmPair (y, ScmNil))))) (List.tl a) (ScmPair (ScmSymbol "quote",(ScmPair (b, ScmNil))))
                     ) in 
  nt1 str;;

let nt_quasi_quoted str = 
  let nt1 = char '\x60' in
  let nt1 = plus nt1 in 
  let nt2 = nt_sexpr in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (a,b)->
                      List.fold_right
                      (fun x y ->(ScmPair (ScmSymbol "quasiquote",(ScmPair (y, ScmNil))))) (List.tl a) (ScmPair (ScmSymbol "quasiquote",(ScmPair (b, ScmNil))))
                    ) in 
  nt1 str;;


let nt_unquote str = 
  let nt1 = char '\x2C' in
  let nt1 = plus nt1 in 
  let nt2 = nt_sexpr in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (a,b)->
                      List.fold_right
                      (fun x y ->(ScmPair (ScmSymbol "unquote",(ScmPair (y, ScmNil))))) (List.tl a) (ScmPair (ScmSymbol "unquote",(ScmPair (b, ScmNil))))
                    ) in 
  nt1 str ;;

let nt_unquote_and_spliced str = 
  let nt1 = word ",@" in
  let nt1 = plus nt1 in 
  let nt2 = nt_sexpr in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (a,b)->
                      List.fold_right
                      (fun x y ->(ScmPair (ScmSymbol "unquote-splicing",(ScmPair (y, ScmNil))))) (List.tl a) (ScmPair (ScmSymbol "unquote-splicing",(ScmPair (b, ScmNil))))
                    ) in 
  nt1 str ;;


let nt_quoted_forms str = 
  let nt1 = disj_list [nt_quoted;nt_quasi_quoted;nt_unquote;nt_unquote_and_spliced] in 
  nt1 str;;

let nt_sexpr str =
    let nt1 =
    disj_list [nt_number; nt_boolean; nt_char; nt_symbol;nt_quoted_forms] in
    let nt1 = make_skipped_star nt1 in
          nt1 str;;