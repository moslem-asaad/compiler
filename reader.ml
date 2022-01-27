(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

 #use "pc.ml";;

 let rec gcd a b =
   match (a, b) with
   | (0, b) -> b
   | (a, 0) -> a
   | (a, b) -> gcd b (a mod b);;
 
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
 
 module type READER = sig
     val nt_sexpr : sexpr PC.parser
 end;; (* end of READER signature *)
 
 module Reader : READER = struct
 open PC;;
 
 
 let char_To_aList_of_char ch = [ch];;
 
 let booleanPackFunction = function 
   | ['#'; 'T'] -> ScmBoolean(true)
   | ['#'; 't'] -> ScmBoolean(true)
   | ['#'; 'F'] -> ScmBoolean(false)
   | ['#'; 'f'] -> ScmBoolean(false)
   | _ -> ScmBoolean(false);;
 
 
 
 let appendToStringss st1 st2 = st1^st2 ;;
 
 let fold_my_list lst = 
 (List.fold_right appendToStringss lst "");;
 
 let nt_disj_list_to_sEx_pack_function lst = 
 ScmString((fold_my_list lst));;
 
 
 let hexacharToOcamlChar st = char_of_int (int_of_string("0X"^st));;
 let char_hex_pack_function (left,right) = hexacharToOcamlChar (list_to_string right);;
 
 let strHexCharPackFunc1  = function
 | [list_ch1; list_ch2; list_ch3; list_ch4] -> (list_to_string (char_To_aList_of_char (char_hex_pack_function (list_ch3,list_ch3)))) ;;
 
 
 let nt_char_pack_function (left, right) = ScmChar(right);;
 let char_list_to_number list = int_of_string (list_to_string list);;
 let nt_int_pack_function (left, right) = match left with
 | Some(char) when char= '-' -> -(right)
 | _ -> right;;
 
 let nt_float_pack_function (left, right) = match left with
 | Some(char) when char= '-' -> ScmReal((-.right))
 | _ -> ScmReal(right);;
 
 let nt_frac_pack_function (first_num , (frac_char ,  sec_num)) = 
 let temp  = gcd first_num sec_num in 
 ScmRational(first_num/temp, sec_num/temp);;
 
 let catenLeftRight (left, right) =  left^right;;
 
 
 let nt_FloatA_pack_function lst = match lst with 
 | [Some(int_part); Some(char_dot); Some(mantissa_part); Some(exponent_part) ] ->   float_of_string (((int_part^char_dot)^mantissa_part)^exponent_part)
 | [Some(int_part); Some(char_dot); None; None] -> float_of_string (int_part^char_dot)
 | [Some(int_part); Some(char_dot); Some(mantissa_part); None] -> float_of_string (int_part^char_dot^mantissa_part)
 | [Some(int_part); Some(char_dot); None; Some(exponent_part)] -> float_of_string (int_part^char_dot^exponent_part);;
 
 let nt_FloatB_pack_function lst = match lst with 
 | [Some(char_dot); Some(mantissa_part); Some(exponent_part)] ->  float_of_string (char_dot^mantissa_part^exponent_part)
 | [Some(char_dot); Some(mantissa_part); None] -> float_of_string (char_dot^mantissa_part);;
 
 let nt_FloatC_pack_function (int_part, exponent_part) = float_of_string(int_part^exponent_part);;
 
 let nt_word1_function st = "\\" ;;
 let nt_word2_function st = "\"" ;;
 let nt_word3_function st = "\t" ;;
 let nt_word4_function st = "\012" ;;
 let nt_word5_function st = "\n" ;;
 let nt_word6_function st = "\r" ;;
 let nt_word7_function st = "~" ;;
 
 
 let rec ocamllst_to_Scmlst = function
 | [] -> ScmNil
 | hd::[] -> ScmPair (hd, ScmNil)
 | hd::tl -> ScmPair (hd, ocamllst_to_Scmlst tl);;
 
 let rec ocamllst_to_ScmImplst = function
 | [] -> ScmNil
 | hd::[] -> hd
 | hd::tl -> ScmPair (hd, ocamllst_to_ScmImplst tl);;
 
 
 
 let stringInterpolatedPackFun33 ((first, secnd), third ) = secnd;;
 
 
 
 let nt_disj_list_to_sEx_nt8_pack_func = function 
 | first::rest when (List.length rest)=0 -> first
 | first::rest -> ocamllst_to_Scmlst ((ScmSymbol "string-append")::(first::rest))
 | [] -> (ScmString "");;
 
 
 let unitify nt = pack nt (fun _ -> ());;
 
 let rec nt_whitespace str =
   const (fun ch -> ch <= ' ') str
 and nt_end_of_line_or_file str =
   let nt1 = unitify (char '\n') in
   let nt2 = unitify nt_end_of_input in
   let nt1 = disj nt1 nt2 in
   nt1 str
 
 and nt_line_comment str = 
   let nt1 = char ';' in 
   let nt2 = nt_end_of_line_or_file in 
   let nt3 = diff nt_any nt2 in 
   let nt3 = star nt3 in 
   let nt1 = caten (caten nt1 nt3) nt2 in 
   let nt1 = unitify nt1 in
   nt1 str
 
 and nt_paired_comment str = 
   let nt1 = char '{' in
   let nt2 = char '}' in 
   let nt3 = diff nt_any nt2 in 
   let nt3 = star nt3 in 
   let nt1 = caten nt1 (caten nt3 nt2) in 
   let nt1 = unitify nt1 in
   nt1 str 
 
 and nt_sexpr_comment str = 
   let nt1 = word "#;" in
   let nts = nt_sexpr in 
   let nt1 = caten nt1 nts in 
   let nt1 = pack nt1 (fun _ -> ()) in 
   nt1 str
 
 and nt_comment str =
   disj_list
     [nt_line_comment;
      nt_paired_comment;
      nt_sexpr_comment] str
 
 and nt_skip_star str =
   let nt1 = disj (unitify nt_whitespace) nt_comment in
   let nt1 = unitify (star nt1) in
   nt1 str
 and make_skipped_star (nt : 'a parser) =
   let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
   let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
   nt1
 
 and nt_Nat = (pack (plus (range_ci '0' '9') ) char_list_to_number)
 and nt_int str = 
   let nt1 = (maybe (disj (char_ci '+') (char_ci '-'))) in 
   (pack (caten nt1 nt_Nat) nt_int_pack_function) str
 
 and nt_frac str = (pack (caten nt_int (caten (char_ci '/') nt_Nat)) nt_frac_pack_function) str
 
 and nt_integer_part str = (pack (plus (range_ci '0' '9') ) list_to_string) str
 and nt_mantissa str = (pack (plus (range_ci '0' '9') ) list_to_string) str
 and nt_ExponentToken str = (pack (disj_list[word "e"; word "E"; word "*10^"; word "*10**"]) (fun lst -> "e") ) str
 
 
 
 and nt_exponent str = (pack (caten nt_ExponentToken (pack nt_int string_of_int) ) catenLeftRight) str 
 and nt_FloatA str =  (pack (caten_list [(pack nt_integer_part (fun l1 -> Some(l1))); (pack (pack (word ".") list_to_string) (fun l1 -> Some(l1))); (maybe nt_mantissa); (maybe nt_exponent)]) nt_FloatA_pack_function) str
 and nt_FloatB str = (pack (caten_list [(pack (pack (word ".") list_to_string) (fun l1 -> Some(l1))); (pack nt_mantissa (fun l1 -> Some(l1))); (maybe nt_exponent)]) nt_FloatB_pack_function) str
 and nt_FloatC str = (pack (caten nt_integer_part nt_exponent) nt_FloatC_pack_function) str
 and nt_float str = 
   let nt1 = (maybe (disj (char_ci '+') (char_ci '-'))) in 
    (pack (caten nt1 (disj_list [nt_FloatA; nt_FloatB; nt_FloatC])) nt_float_pack_function) str
 
 and nt_number str =
   let nt1 = nt_float in
   let nt2 = nt_frac in
   let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
   let nt1 = disj nt1 (disj nt2 nt3) in
   let nt1 = pack nt1 (fun r -> ScmNumber r) in
   let nt1 = not_followed_by nt1 nt_symbol_char in
   nt1 str
 and nt_boolean str = (pack (disj (word_ci("#f")) (word_ci("#t"))) booleanPackFunction) str
 
 and nt_char_simple str = (const (fun ch -> ch > ' ')) str
 
 and make_named_char char_name ch = (pack (disj (word char_name) (word_ci char_name)) (fun _ -> ch))
 and nt_char_named str =
   let nt1 =
     disj_list [(make_named_char "newline" '\n');
                (make_named_char "page" '\012');
                (make_named_char "return" '\r');
                (make_named_char "space" ' ');
                (make_named_char "tab" '\t')] in
   nt1 str
 
 and nt_char_hex str = (pack (caten (char_ci('X')) (plus(disj (range_ci 'A' 'F') (range_ci '0' '9')))) char_hex_pack_function) str
 
 and nt_char str = (pack (caten (word_ci "#\\") (disj_list [nt_char_hex; nt_char_named; nt_char_simple] )) nt_char_pack_function ) str
 
 and nt_symbol_char str = (disj_list [(range '0' '9'); (range 'a' 'z'); (range 'A' 'Z'); (one_of "!$^*-_=+-<>?/:")]) str
 and nt_symbol str =
   let nt1 = plus nt_symbol_char in
   let nt1 = pack nt1 list_to_string in
   let nt1 = pack nt1 (fun name -> ScmSymbol name) in
   let nt1 = diff nt1 nt_number in
   nt1 str
 
 and stringLiteralChar str = (pack (const (fun ch -> ((ch='\\')=false) && ((ch='~')=false) && ((ch='"')=false) )) (fun ch -> list_to_string (char_To_aList_of_char ch))) str
 and nt_word1 = (pack (word_ci "\\\\") nt_word1_function)
 and nt_word2 = (pack (word_ci "\\\"") nt_word2_function)
 and nt_word3 = (pack (word_ci "\\t") nt_word3_function)
 and nt_word4 = (pack (word_ci "\\f") nt_word4_function)
 and nt_word5 = (pack (word_ci "\\n") nt_word5_function)
 and nt_word6 = (pack (word_ci "\\r") nt_word6_function)
 and nt_word7 = (pack (word_ci "~~") nt_word7_function)
 
 and stringMetaChar str = (disj_list [nt_word1;nt_word2;nt_word3;nt_word4;nt_word5;nt_word6;nt_word7]) str
 and stringHexChar str = (pack (caten_list[(pack (char_ci '\\') (fun ch -> (char_To_aList_of_char ch))); (pack (char_ci 'x') (fun ch -> (char_To_aList_of_char ch))); (plus(disj (range_ci 'A' 'F') (range_ci '0' '9'))); (pack (char_ci ';') (fun ch -> (char_To_aList_of_char ch)))]) strHexCharPackFunc1 ) str
 and stringInterpolated str = (pack (caten (caten (word "~{") nt_sexpr) (word "}")) stringInterpolatedPackFun33 ) str
 
 and nt_disj_list_to_sEx str = 
 let nt1 = stringLiteralChar in
 let nt2 = stringMetaChar in 
 let nt3 = stringHexChar in
 let nt4 = (pack stringInterpolated (fun sexp1 -> ScmPair(ScmSymbol("format"), ScmPair(ScmString("~a"), ScmPair(sexp1 , ScmNil)))) ) in
 let nt5 str = (pack (plus (disj_list [nt1; nt2; nt3])) nt_disj_list_to_sEx_pack_function) str in 
 let nt6 = (disj nt4 nt5) in 
 let nt7 = (star nt6) in
 let nt8 = pack nt7 nt_disj_list_to_sEx_nt8_pack_func in
 nt8 str
 
 and nt_string str =  (pack (caten (caten (char '"') nt_disj_list_to_sEx) (char '"')) stringInterpolatedPackFun33 ) str
 
 
 
 and nt_vector str =
   let nt1 = word "#(" in
   let nt2 = caten nt_skip_star (char ')') in
   let nt2 = pack nt2 (fun _ -> ScmVector []) in
   let nt3 = plus nt_sexpr in
   let nt4 = char ')' in
   let nt3 = caten nt3 nt4 in
   let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
   let nt2 = disj nt2 nt3 in
   let nt1 = caten nt1 nt2 in
   let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
   nt1 str
 
 and nt_ProperList str =
   let nt1 = word "(" in
   let nt2 = caten nt_skip_star (char ')') in
   let nt2 = pack nt2 (fun _ -> (ocamllst_to_Scmlst [])) in
   let nt3 = plus nt_sexpr in
   let nt4 = char ')' in
   let nt3 = caten nt3 nt4 in
   let nt3 = pack nt3 (fun (sexprs, _) -> (ocamllst_to_Scmlst sexprs)) in
   let nt2 = disj nt2 nt3 in
   let nt1 = caten nt1 nt2 in
   let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
   nt1 str
   
 
 and nt_ImproperList str =
   let nt1 = word "(" in
   let nt1 = pack (caten nt1 (plus nt_sexpr)) (fun (_, sexpr) -> sexpr) in
   let nt1 = pack (caten nt1 (word ".")) (fun (sexpr, _) -> sexpr) in
   let nt1 = pack (caten nt1 nt_sexpr) (fun (sexpr1 , sexpr2) -> sexpr1@[sexpr2]) in
   let nt1 = pack (caten nt1 ( word ")" )) (fun (sexpr, _) -> sexpr) in
   let nt1 = pack nt1 ocamllst_to_ScmImplst in
   nt1 str
 
 and nt_list str = (disj nt_ProperList nt_ImproperList) str
 
 and nt_Quoted str = (pack (caten (word "'") nt_sexpr) (fun (w,sexpr1) -> ScmPair(ScmSymbol("quote"), ScmPair(sexpr1,ScmNil)))) str
 and nt_QuasiQuoted str = (pack (caten (word "`") nt_sexpr) (fun (w,sexpr1) -> ScmPair(ScmSymbol("quasiquote"), ScmPair(sexpr1,ScmNil)))) str
 and nt_UnQuoted str = (pack (caten (word ",") nt_sexpr) (fun (w,sexpr1) -> ScmPair(ScmSymbol("unquote"), ScmPair(sexpr1,ScmNil)))) str
 and nt_UnQuoteAndSpliced str = (pack (caten (word ",@") nt_sexpr) (fun (w,sexpr1) -> ScmPair(ScmSymbol("unquote-splicing"), ScmPair(sexpr1,ScmNil)))) str
 and nt_quoted_forms str = (disj_list [nt_Quoted; nt_QuasiQuoted; nt_UnQuoted; nt_UnQuoteAndSpliced]) str
 
 and nt_sexpr str =
   let nt1 =
     disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
                nt_string; nt_vector; nt_list; nt_quoted_forms] in
   let nt1 = make_skipped_star nt1 in
   nt1 str;;
 
 end;; (* end of struct Reader *)
 
 
 let rec string_of_sexpr = function
   | ScmVoid -> "#<void>"
   | ScmNil -> "()"
   | ScmBoolean(false) -> "#f"
   | ScmBoolean(true) -> "#t"
   | ScmChar('\n') -> "#\\newline"
   | ScmChar('\r') -> "#\\return"
   | ScmChar('\012') -> "#\\page"
   | ScmChar('\t') -> "#\\tab"
   | ScmChar(' ') -> "#\\space"
   | ScmChar(ch) ->
      if (ch < ' ')
      then let n = int_of_char ch in
           Printf.sprintf "#\\x%x" n
      else Printf.sprintf "#\\%c" ch
   | ScmString(str) ->
      Printf.sprintf "\"%s\""
        (String.concat ""
           (List.map
              (function
               | '\n' -> "\\n"
               | '\012' -> "\\f"
               | '\r' -> "\\r"
               | '\t' -> "\\t"
               | ch ->
                  if (ch < ' ')
                  then Printf.sprintf "\\x%x;" (int_of_char ch)
                  else Printf.sprintf "%c" ch)
              (string_to_list str)))
   | ScmSymbol(sym) -> sym
   | ScmNumber(ScmRational(0, _)) -> "0"
   | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
   | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
   | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
   | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
   | ScmVector(sexprs) ->
      let strings = List.map string_of_sexpr sexprs in
      let inner_string = String.concat " " strings in
      Printf.sprintf "#(%s)" inner_string
   | ScmPair(ScmSymbol "quote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "'%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "quasiquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "`%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote-splicing",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",@%s" (string_of_sexpr sexpr)
   | ScmPair(car, cdr) ->
      string_of_sexpr' (string_of_sexpr car) cdr
 and string_of_sexpr' car_string = function
   | ScmNil -> Printf.sprintf "(%s)" car_string
   | ScmPair(cadr, cddr) ->
      let new_car_string =
        Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
      string_of_sexpr' new_car_string cddr
   | cdr ->
      let cdr_string = (string_of_sexpr cdr) in
      Printf.sprintf "(%s . %s)" car_string cdr_string;;
 
 