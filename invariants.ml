open Printf

(* Définitions de terme, test et programme *)
type term = 
 | Const of int
 | Var of int
 | Add of term * term
 | Mult of term * term

type test = 
 | Equals of term * term
 | LessThan of term * term
 | GreaterOrEqual of term * term
 | GreaterThan of term * term
 | LessOrEqual of term * term
 | Different of term * term

let tt = Equals (Const 0, Const 0)
let ff = LessThan (Const 0, Const 0)
 
type program = {nvars : int; 
                inits : term list; 
                mods : term list; 
                loopcond : test; 
                assertion : test}

let x n = "x" ^ string_of_int n

let rec str_of_term t = 
  match t with
  | Const(n) -> string_of_int n
  | Var(n) -> x n
  | Add(t1,t2) ->
     "(+ " ^ (str_of_term t1) ^ " " ^ (str_of_term t2) ^ ")"
  | Mult(t1,t2) ->
     "(* " ^ (str_of_term t1) ^ " " ^ (str_of_term t2) ^ ")"

let str_of_test t =
  match t with
  | Equals(t1,t2) ->
     "(= " ^ (str_of_term t1) ^ " " ^ (str_of_term t2) ^ ")"
  | LessThan(t1,t2) ->
     "(< " ^ (str_of_term t1) ^ " " ^ (str_of_term t2) ^ ")"
  | GreaterOrEqual(t1,t2) ->
     "(>= " ^ (str_of_term t1) ^ " " ^ (str_of_term t2) ^ ")"
  | LessOrEqual(t1,t2) ->
     "(<= " ^ (str_of_term t1) ^ " " ^ (str_of_term t2) ^ ")"
  | GreaterThan(t1,t2) ->
     "(> " ^ (str_of_term t1) ^ " " ^ (str_of_term t2) ^ ")"
  | Different(t1,t2) ->
     "(!= " ^ (str_of_term t1) ^ " " ^ (str_of_term t2) ^ ")"

let opposite t =
  match t with
  | Equals(t1,t2) ->
     Different(t1,t2)
  | LessThan(t1,t2) ->
     GreaterOrEqual(t1,t2)
  | GreaterOrEqual(t1,t2) ->
     LessThan(t1,t2)
  | LessOrEqual(t1,t2) ->
     GreaterThan(t1,t2)
  | GreaterThan(t1,t2) ->
     LessOrEqual(t1,t2)
  | Different(t1,t2) ->
     Equals(t1,t2)

let string_repeat s n =
  Array.fold_left (^) "" (Array.make n s)

let str_condition l = 
  match l with
  | [] -> failwith "empty list"
  | v :: vs ->
    let rec str_condition_aux list =
      match list with
      | [] -> ")"
      | t :: ts -> 
        " " ^ (str_of_term t) ^ (str_condition_aux ts)
    in
    "(Invar " ^ (str_of_term v)^(str_condition_aux vs)   

let str_assert s = "(assert " ^ s ^ ")"

(* concats (xi Int) n times with i from 1 to n included *)
let rec concatxint (i:int) (n:int) =
  let str = "(" ^ (x i) ^ " Int)" in
  if n = 1 then
    str
   else
     str ^ " " ^ concatxint (i+1) (n-1)

let rec concatxn (i:int) (n:int) : string =
  if n = 1 then
    x i
  else
    x i ^ " " ^ concatxn (i+1) (n-1)

let str_assert_forall n s =
  "(forall (" ^ concatxint 1 n ^ ") (" ^ s ^ "))"

let smtlib_of_wa p = 
  let declare_invariant n =
    "; synthèse d'invariant de programme\n"
    ^"; on déclare le symbole non interprété de relation Invar\n"
    ^"(declare-fun Invar (" ^ string_repeat "Int " n ^  ") Bool)"
  in
  let loop_condition p =
    "; la relation Invar est un invariant de boucle\n"
    ^ str_assert
        (str_assert_forall p.nvars
           ("=> (and (Invar " ^ concatxn 1 p.nvars ^ ") "
            ^ (str_of_test p.loopcond) ^ ") " ^ (str_condition p.mods)))
  in
  let initial_condition p =
    "; la relation Invar est vraie initialement\n"
    ^str_assert (str_condition p.inits)
  in
  let assertion_condition p =
    "; l'assertion finale est vérifiée\n"
    ^ str_assert
        (str_assert_forall p.nvars
           ("=> (and (Invar " ^ concatxn 1 p.nvars ^ ") "
            ^ (str_of_test (opposite p.loopcond)) ^ ") "
            ^ (str_of_test p.assertion )))
  in
  let call_solver =
    "; appel au solveur\n(check-sat-using (then qe smt))\n(get-model)\n(exit)\n"
  in
  String.concat "\n" [declare_invariant p.nvars;
                      loop_condition p;
                      initial_condition p;
                      assertion_condition p;
                      call_solver]

let p1 = {nvars = 2;
          inits = [(Const 0) ; (Const 0)];
          mods = [Add ((Var 1), (Const 1)); Add ((Var 2), (Const 3))];
          loopcond = LessThan ((Var 1),(Const 3));
          assertion = Equals ((Var 2),(Const 9))}


let () = Printf.printf "%s" (smtlib_of_wa p1)

let p2 = {nvars = 2;
          inits = [(Const 2) ; (Const 1)];
          mods = [Add ((Var 1), (Const 2)); Add ((Var 2), (Var 1))];
          loopcond = LessThan ((Var 1),(Const 10));
          assertion = GreaterOrEqual ((Var 2),(Const 15))}

(* let () = Printf.printf "%s" (smtlib_of_wa p2) *)
