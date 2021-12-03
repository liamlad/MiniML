(** Template Begins Here *)

(* Q0  : Get familiar with the external syntax of MiniML *)
let parse_tests : (string * (string, exp) either) list = [
    (* Provide your tests for the parser *)
    ("1;", Right (Int 1));
    ("let fun fact (x : int ) : int =
        if x = 0 then
          1
        else
          x * fact (x - 1)
      in
        fact 5
      end;", Right (
        Let ([ Val
          (Rec ("fact", TArrow (TInt, TInt), 
            Fn (
              "x", Some TInt, 
              If ( 
                Primop (Equals, [Var "x"; Int 0]), 
                Int 1, 
                Primop (Times, [Var "x"; 
                                Apply (Var "fact", 
                                Primop (Minus, [Var "x"; Int 1]))])))),
        "fact")], 
        Apply (Var "fact", Int 5))));
    ("(1, 2);", Right (Tuple [Int 1; Int 2]))
]


let free_vars_tests : (exp * name list) list = [
  (Int 10, []);
  (If (
    Primop (Equals, [Var "x"; Int 0]),
    Let ([
      Val (Int 1, "y")
    ], Primop (Plus, [Var "y"; Int 1])),
    Int 4
  ), ["x"]);
  ((Let
    ([Val
      (Rec ("apply", TArrow (TArrow (TInt, TInt), TArrow (TInt, TInt)),
        Fn
          ("f", Some (TArrow (TInt, TInt)),
            Fn ("x", Some TInt, Apply (Var "f", Var "x")))),
      "apply")],
    Apply
      (Apply (Var "apply", Fn ("x", None, Primop (Times, [Var "x"; Int 3]))),
      Int 100))), []);
  ((Primop (Plus, [Var "x"; Int 5])), ["x"]);
  ((Let
  ([Valtuple
     (Tuple [Primop (Plus, [Int 2; Int 1]); Primop (Times, [Int 2; Int 50])],
     ["x"; "y"])],
  Primop (Times, [Var "z"; Var "z"]))), ["z"]);
  ((Let
  ([Val (Let ([Val (Var "x", "y")], Primop (Plus, [Var "y"; Var "x"])), "x")],
  Primop (Plus, [Var "x"; Int 1]))), ["x"]);
  ((Let
  ([Val (Int 1, "x"); Val (Primop (Plus, [Int 1; Var "x"]), "y");
    Val (Primop (Plus, [Primop (Plus, [Int 1; Var "x"]); Var "y"]), "z")],
  Primop (Plus,
   [Primop (Plus, [Primop (Plus, [Var "x"; Var "y"]); Var "z"]); Var "w"]))), ["w"]);
  ((Let ([Valtuple (Tuple [Int 2; Var "x"], ["x"; "y"])], Var "y")), ["x"])
]
let rec extract_names (dl : dec list) acc = match dl with 
  | [] -> acc
  | d::t -> match d with
    | Val (e, n) -> extract_names t (n::acc)
    | Valtuple (e, nl) -> extract_names t (nl@acc)
    | ByName (e, n) -> extract_names t (n::acc)

let rec extract_expr (dl : dec list) acc = match dl with
  | [] -> acc
  | d::t -> match d with
    | Val (e, n) -> extract_expr t (e::acc)
    | Valtuple (e, nl) -> extract_expr t (e::acc)
    | ByName (e, n) -> extract_expr t (e::acc)


(* Q1  : Find the free variables in an expression *)
let rec free_vars (e : exp) : name list =  
  let rec free_let dl names = match dl with
    | [] -> []
    | h::t -> match h with 
      | Val (e, n) -> union (delete names (free_vars e)) (free_let t (n::names))
      | Valtuple (e, nl) -> union (delete names (free_vars e)) (free_let t (nl@names))
      | ByName (e, n) -> union (delete names (free_vars e)) (free_let t (n::names))

  in match e with
  | Int _ -> []
  | Bool _ -> []
  | If (e, e1, e2) -> union (free_vars e) (union (free_vars e1) (free_vars e2))
  | Primop (_, l) -> union_list (List.map free_vars l)
  | Tuple l -> union_list (List.map free_vars l)
  | Fn (n, t, e) -> delete [n] (free_vars e)
  | Rec (n, t, e) -> delete [n] (free_vars e)
  | Let (l, e) -> union (free_let l []) (delete (extract_names l []) (free_vars e))
    (*union (union_list (List.map free_vars (extract_expr l [])))
                        (delete (extract_names l []) (free_vars e)) *)
  | Apply (e1, e2) -> union (free_vars e1) (free_vars e2)
  | Var x -> [x]
  | Anno (e, t) -> free_vars e


let unused_vars_tests : (exp * name list) list = [
  ((Let ([Val (Int 3, "x")], Int 4)), ["x"]);
  ((Let ([Val (Bool true, "x")],
      Let ([Val (Int 4, "y")], Primop (Plus, [Var "x"; Int 5])))), ["y"]);
  ((Let ([Val (Int 3, "x")],
  Let ([Val (Int 4, "x")], Primop (Plus, [Var "x"; Var "x"])))), ["x"]);
  ((Let
  ([Val (Rec ("test", TArrow (TInt, TInt), Fn ("x", Some TInt, Int 3)),
     "test")],
  Int 4)), ["x"; "test"]);
  ((Let ([Val (Int 2, "x"); Val (Int 4, "x")], Var "x")), ["x"]);
  ((Let ([Val (Int 4, "x"); Val (Var "x", "x")], Var "x")), []);
  ((Let
  ([Val (Rec ("test", TArrow (TInt, TInt), Fn ("x", Some TInt, Int 3)),
     "test")],
  Apply (Var "test", Int 4))), ["x"]);
  ((Let ([Val (Int 2, "x"); Val (Int 3, "x"); Val (Int 4, "x")], Var "x")), ["x"]);
  ((Let
    ([Valtuple (Int 3, ["x"; "y"; "z"]);
      Valtuple (Int 4, ["x"; "y"; "z"; "w"; "p"]); Val (Int 1, "w");
      Val (Int 5, "p"); Valtuple (Int 0, ["q"; "p"])],
      Primop (Plus,
        [Primop (Plus,
          [Primop (Plus, [Primop (Plus, [Var "x"; Var "y"]); Var "z"]); Var "p"]);
          Var "w"]))), ["x"; "y"; "z"; "w"; "p"; "q"]);
  ((Let ([Valtuple (Tuple [Int 2; Var "x"], ["x"; "y"])], Var "x")),["y"]);
  ((Tuple
  [Let ([Val (Int 4, "x")], Int 5); Let ([Val (Int 5, "y")], Int 6);
   Let ([Val (Primop (Plus, [Var "x"; Var "y"]), "z")], Int 7)]), ["x";"y";"z"]);
  ((Let
  ([Val (Primop (Plus, [Var "x"; Int 2]), "x"); Val (Int 4, "y");
    Val (Int 3, "z")],
  Primop (Plus, [Var "y"; Var "z"]))), ["x"]);
  ((Let ([Val (Int 3, "x")],
  Let ([Val (Var "x", "y")], Let ([Val (Int 1, "z")], Int 4)))), ["y";"z"]);
  ((Let
  ([Val
     (Rec ("f", TArrow (TInt, TInt),
       Fn ("x", Some TInt, Primop (Plus, [Var "x"; Apply (Var "f", Var "x")]))),
     "f")],
  Int 1)), ["f"])
]

let rec get_unused names free acc =
  match names with
  | [] -> acc
  | h::t -> if member h free then get_unused t free acc
            else get_unused t free (h::acc)

let rec remove_once el set acc= 
  match set with 
  | [] -> acc
  | h::t -> if h = el then acc@t else remove_once el t (h::acc)

let rec delete_once ds set = 
  match set with
  | [] -> []
  | h::t -> if member h ds then delete_once (remove_once h ds []) t
            else h :: delete_once ds t
    


(* Q2  : Check variables are in use *)
let rec unused_vars (e : exp) : name list = 
  match e with
    | Int _ -> []
    | Bool _ -> []
    | If (e1, e2, e3) -> union (unused_vars e1) (union (unused_vars e2) (unused_vars e3))
    | Primop (_, l) -> union_list (List.map unused_vars l)
    | Tuple (l) -> union_list (List.map unused_vars l)
    | Fn (n, t, e1) -> let free = free_vars e1 in
        if member n free then unused_vars e1 else
          union [n] (unused_vars e1)
    | Rec (n, t, e1) -> let free = free_vars e1 in
        if member n free then unused_vars e1 else
          union [n] (unused_vars e1)
    | Let (dl, e1) -> (match dl with
          | [] -> unused_vars e1
          | h::t -> match h with
              | Val (e, n) -> if member n (free_vars (Let (t, e1))) then 
                              union (delete [n] (unused_vars e)) (unused_vars (Let (t, e1)))
                              else union (unused_vars e) (union [n] (unused_vars (Let (t, e1))))
              | Valtuple (e, nl) -> let free = free_vars (Let (t, e1)) in
                                    union (delete nl (unused_vars e)) (union (delete_once free nl) (unused_vars (Let (t, e1))))
              | ByName (e, n) -> if member n (free_vars (Let (t, e1))) then 
                                  union (unused_vars e) (unused_vars (Let (t, e1)))
                                  else union (delete [n] (unused_vars e)) (union [n] (unused_vars (Let (t, e1)))))
    | Apply (e1, e2) -> union (unused_vars e1) (unused_vars e2)
    | Var x -> []
    | Anno (e1, t) -> unused_vars e1


let subst_tests : (((exp * name) * exp) * exp) list = [
  ((((Primop (Plus, [Var "q"; Int 4])), "p"), (Let
  ([Val (Int 5, "x"); Val (Primop (Plus, [Var "x"; Int 3]), "y");
    Val (Primop (Plus, [Var "p"; Int 7]), "z")],
  Primop (Plus, [Var "p"; Int 4])))), (Let
  ([Val (Int 5, "x"); Val (Primop (Plus, [Var "x"; Int 3]), "y");
    Val (Primop (Plus, [Primop (Plus, [Var "q"; Int 4]); Int 7]), "z")],
  Primop (Plus, [Primop (Plus, [Var "q"; Int 4]); Int 4]))));
  (((Int 10, "x"), (Let ([Val (Primop (Plus, [Var "x"; Int 10]), "x"); Val (Int 10, "y")],
  Primop (Plus, [Var "x"; Var "y"])))), (Let ([Val (Primop (Plus, [Int 10; Int 10]), "x"); Val (Int 10, "y")],
  Primop (Plus, [Var "x"; Var "y"]))));
  ((((Primop (Plus, [Var "x"; Int 10])), "q"), (Let
  ([Val (Int 10, "x"); Val (Int 11, "y");
    Valtuple (Tuple [Primop (Plus, [Var "x"; Var "q"]); Var "y"], ["z"; "q"])],
  Primop (Plus,
   [Primop (Plus, [Primop (Plus, [Var "x"; Var "y"]); Var "z"]); Var "q"])))), Int 10)
  (*(((e', x), exp), result);*)

]



(* Q3  : Substitute a variable *)
let rec subst ((e', x) : exp * name) (e : exp) : exp =
   match e with
  | Var y ->
     if x = y then
       e'
     else
       Var y

  | Int _ | Bool _ -> e
  | Primop (po, es) -> Primop (po, List.map (subst (e', x)) es)
  | If (e1, e2, e3) -> If (subst (e', x) e1, subst (e', x) e2, subst (e', x) e3)
  | Tuple es -> Tuple (List.map (subst (e', x)) es)
  | Anno (e, t) -> Anno (subst (e', x) e, t)

  | Let (dl, e2) -> begin if member x (free_vars e) then 
    match dl with
    | [] -> Let (dl, subst (e', x) e2)
    | h::t -> match h with
      | Val (e3, n) -> if member n (free_vars e') then let new_var = fresh_var n in
        let Let (dl1, e4) = subst (Var (new_var), n) (Let (t, e2)) in
        subst (e',x) (Let (Val (e3, new_var)::dl1, e4))
        else if n = x then Let (Val (subst (e', x) e3, n)::t, e2)
        else let Let (dl1, e4) = subst (e',x) (Let (t, e2)) in 
        Let (Val (subst (e', x) e3, n)::dl1, e4)
      | Valtuple (e3, nl) -> if member x nl then Let (Valtuple (subst (e', x) e3, nl)::t, e2)
        else let Let (dl1, e4) = subst (e', x) (Let (t, e2)) in 
        Let (Valtuple (subst (e', x) e3, nl)::dl1, e4)
      | ByName (e3, n) -> if member n (free_vars e') then let new_var = fresh_var n in
        let Let (dl1, e4) = subst (Var (new_var), n) (Let (t, e2)) in
        subst (e',x) (Let (ByName (e3, new_var)::dl1, e4))
        else if n = x then Let (ByName (subst (e', x) e3, n)::t, e2)
        else let Let (dl1, e4) = subst (e',x) (Let (t, e2)) in 
        Let (Val (subst (e', x) e3, n)::dl1, e4)
    else Let (dl, e2) end

  | Apply (e1, e2) -> Apply (subst (e', x) e1, subst (e', x) e2)
  | Fn (y, t, e) -> if member x (free_vars e) then if y = x then Fn (y, t, e) else 
    if member y (free_vars e') then let new_func = fresh_var y in Fn (new_func, t, subst (e', x) (subst (Var new_func, y) e))
    else Fn (y, t, subst (e', x) e)
    else Fn (y, t, e)
  | Rec (f, t, e) -> if member x (free_vars e) then if f = x then Rec (f, t, e) else 
    if member f (free_vars e') then let new_func = fresh_var f in Rec (new_func, t, subst (e', x) (subst (Var new_func, f) e))
    else Rec (f, t, subst (e', x) e)
    else Rec (f, t, e)


let eval_tests : (exp * exp) list = [
  ((Let
  ([Val
     (Rec ("apply", TArrow (TArrow (TInt, TInt), TArrow (TInt, TInt)),
       Fn
        ("f", Some (TArrow (TInt, TInt)),
         Fn ("x", Some TInt, Apply (Var "f", Var "x")))),
     "apply")],
  Apply
   (Apply (Var "apply", Fn ("x", None, Primop (Times, [Var "x"; Int 3]))),
   Int 100))), Int 300);
  ((Let
  ([Val
     (Rec ("fact", TArrow (TInt, TInt),
       Fn
        ("x", Some TInt,
         If (Primop (Equals, [Var "x"; Int 0]), Int 1,
          Primop (Times,
           [Var "x"; Apply (Var "fact", Primop (Minus, [Var "x"; Int 1]))])))),
     "fact")],
  Apply (Var "fact", Int 5))), Int 120)
]

(* Q4  : Evaluate an expression in big-step *)  
let rec eval : exp -> exp =
  (* do not modify from here *)
  let bigstep_depth = ref 0 in
    fun e ->
      if !debug >= 1 then
        print_endline
          (String.make (!bigstep_depth) ' '
          ^ "eval (" ^ Print.exp_to_string e ^ ")\n");
      incr bigstep_depth;
    (* to here *)
      let result =
        match e with
        | Int _ | Bool _ -> e
        | Tuple es -> Tuple (List.map eval es)
        | If (e1, e2, e3) ->
            begin match eval e1 with
              | Bool b ->
                  if b then
                    eval e2
                  else
                    eval e3
              | _ -> stuck "Condition for if expression should be of the type bool"
            end
        | Anno (e, _) -> eval e     (* types are ignored in evaluation *)
        | Var x -> stuck ("Free variable \"" ^ x ^ "\" during evaluation")

        | Fn (x, t, e) -> Fn (x, t, e)

        | Apply (e1, e2) -> begin try let Fn (x, t, e3) = eval e1 in let v2 = eval e2 in eval (subst (v2, x) e3)
          with _ -> stuck "Cannot apply if first argument is not a function!" end
            
        | Rec (f, t, e) -> eval (subst (Rec (f, t, e), f) e)

        | Primop (And, es) -> let vs = List.map eval es in 
          begin match vs with
          | [Bool a; Bool b] -> Bool (a && b)
          | _ -> stuck "And operation takes as input two bools!" end
        
        | Primop (Or, es) -> let vs = List.map eval es in 
          begin match vs with
          | [Bool a; Bool b] -> Bool (a || b)
          | _ -> stuck "Or operation takes as input two bools!" end

        | Primop (op, es) ->
            let vs = List.map eval es in
            begin match eval_op op vs with
              | None -> stuck "Bad arguments to primitive operation"
              | Some v -> v
            end

        | Let (ds, e) -> begin match ds with
            | [] -> eval e
            | h::t -> match h with
              | Val (e1, n) -> let v1 = eval e1 in eval (subst (v1, n) (Let (t, e)))
              | ByName (e1, n) -> eval (subst (e1, n) (Let (t, e)))
              | Valtuple (e1, nl) -> let vs = eval (e1) in begin match vs with
                | Tuple el -> if List.length nl = List.length el then let combined = List.combine el nl in eval (List.fold_right subst combined (Let (t, e)))
                else stuck "Size of tuples did not match!"
                | _ -> stuck "Expression did not evaluate to a tuple!"


              end end
      in
    (* do not change the code from here *)
      decr bigstep_depth;
      if !debug >= 1 then
        print_endline
          (String.make (!bigstep_depth) ' '
          ^ "result of eval (" ^ Print.exp_to_string e ^ ") = "
          ^ Print.exp_to_string result ^ "\n");
    (* to here *)
      result


let infer_tests : ((context * exp) * typ) list = [
  ((Ctx ([]), (Let
  ([Val
     (Let ([Val (Int 10, "ten")],
       Anno (Fn ("y", None, Var "ten"), TArrow (TInt, TInt))),
     "f")],
  Apply (Var "f", Int 55)))), TInt);
  ((Ctx [],  (Let
  ([Val
     (Rec ("repeat",
       TArrow (TInt, TArrow (TArrow (TInt, TInt), TArrow (TInt, TInt))),
       Fn
        ("n", Some TInt,
         Fn
          ("f", Some (TArrow (TInt, TInt)),
           Fn
            ("x", Some TInt,
             If (Primop (Equals, [Var "n"; Int 0]), Var "x",
              Apply
               (Apply (Apply (Var "repeat", Primop (Minus, [Var "n"; Int 1])),
                 Var "f"),
               Apply (Var "f", Var "x"))))))),
     "repeat")],
  Apply
   (Apply (Apply (Var "repeat", Int 4),
     Fn ("z", Some TInt, Primop (Times, [Var "z"; Int 2]))),
   Int 100)))), TInt);
   ((Ctx [], (Fn
   ("x", None,
    Fn
     ("p", None,
      Let ([Valtuple (Var "x", ["x1"; "x2"])],
       If (Primop (GreaterThan, [Apply (Var "p", Var "x1"); Int 3]), 
        Var "x2", Var "x1")))))), TInt);
    ((Ctx [], (Fn ("f", None, Fn ("x", None, Apply (Var "f", Apply (Var "f", Var "x")))))), TInt);
    ((Ctx [],  (Let ([Valtuple (Tuple [Int 3; Int 4; Var "f"], ["x"; "y"; "z"])],
    Primop (Plus, [Var "x"; Var "y"])))), TInt)


]


let unify_tests : ((typ * typ) * unit) list = [
  ((fresh_tvar (), TInt), ());
  ((TArrow (fresh_tvar (), TBool), TArrow (TInt, fresh_tvar ())), ());
  ((TProduct [fresh_tvar (); TBool], TProduct [TInt; TBool]), ());
  ((fresh_tvar (), TProduct [fresh_tvar (); fresh_tvar ()] ), ())
]

let rec occ_check (TVar a) t = 
  match t with
  | TInt -> true
  | TBool -> true
  | TArrow (t1, t2) -> occ_check (TVar a) t1 && occ_check (TVar a) t2
  | TProduct tl -> List.fold_left (&&) true (List.map (occ_check (TVar a)) tl)
  | TVar b -> not (typ_eq (TVar a) (TVar b))

(* find the next function for Q5 *)
(* Q6  : Unify two types *)
let rec unify (ty1 : typ) (ty2 : typ) : unit = 
  match ty1, ty2 with
  | TInt, TInt -> ()
  | TBool, TBool -> ()
  | TArrow (t1, t2), TArrow (s1, s2) -> unify t1 s1; unify t2 s2
  | TProduct tl1, TProduct tl2 -> if List.length tl1 = List.length tl2 then 
    begin match tl1, tl2 with
    | [],[] -> ()
    | h1::t1, h2::t2 -> unify h1 h2; unify (TProduct t1) (TProduct t2) end
    else type_fail "Product lengths must match!"
  | TVar a, TVar b -> begin match !a, !b with
    | None, None -> a:= Some (TVar b)
    | Some t, None -> b := Some (TVar a)
    | None, Some t -> a := Some (TVar b)
    | Some t1, Some t2 -> unify t1 t2
     end
  | TVar a, t | t, TVar a -> begin match !a with
     | None -> if occ_check (TVar a) t then a := Some t else type_fail "Could not be unified!"
     | Some t2 -> unify t2 t end
  | _ -> type_fail "Could not be unified!"


(* Q5  : Type an expression *)
(* Q7* : Implement the argument type inference
         For this question, move this function below the "unify". *)

let rec tproduct n acc= 
  if n = 0 then TProduct (acc)
  else let a = fresh_tvar () in 
  tproduct (n-1) (a::acc)

let rec infer (ctx : context) (e : exp) : typ = 
  
  match e with
    | Int _ -> TInt
    | Bool _ -> TBool
    | If (e1, e2, e3) -> begin try unify (infer ctx e1) TBool; 
      begin try unify (infer ctx e2) (infer ctx e3); infer ctx e2 with _ -> type_fail "Types of branches must match!" end
      with _ -> type_fail "If condition must be of type Bool!" end
    
    | Primop (op, el) -> begin match op with
      | Plus | Minus | Times | Div -> begin match el with
        | [e1; e2] -> (try unify (infer ctx e1) TInt; unify (infer ctx e2) TInt; TInt with _ -> type_fail "This operation takes two Ints as input!")
        | _ -> type_fail "This operation takes two Ints as input!" end

      | Equals | NotEquals | LessThan | LessEqual | GreaterThan | GreaterEqual -> begin match el with
        | [e1; e2] -> (try unify (infer ctx e1) TInt; unify (infer ctx e2) TInt; TBool with _ -> type_fail "This operation takes two Ints as input!")
        | _ -> type_fail "This operation takes two TInt as input!" end

      | And | Or -> begin match el with
        | [e1; e2] -> (try unify (infer ctx e1) TBool; unify (infer ctx e2) TBool; TBool with _ -> type_fail "This operation takes two Bools as input!")
        | _ -> type_fail "This operation takes two Bools as input!" end
      
      | Negate -> begin match el with
        | [e1] -> (try unify (infer ctx e1) TInt; TInt with _ -> type_fail "This operation takes a single Int as input!")
        | _ -> type_fail "This operation takes a single Int as input!" end
  
    end
    | Tuple tl -> TProduct (List.map (infer ctx) tl)
    | Fn (x, t, e) -> (match t with 
      | None -> let tv = fresh_tvar () in TArrow (tv, infer (extend ctx (x, tv)) e)
      | Some t -> TArrow (t, infer (extend ctx (x, t))  e))
    | Rec (n, t, e) -> (try unify (infer (extend ctx (n, t)) e) t; t with _ -> type_fail "Recursive type must match!")
    
    | Let (dl, e) -> (match dl with
      | [] -> infer ctx e
      | h::t -> (match h with
        | Val (e1, n) -> infer (extend ctx (n, infer ctx e1)) (Let (t, e))
        | Valtuple (e1, nl) -> begin let t1 = tproduct (List.length nl) [] in 
          try unify (infer ctx e1) t1; let TProduct vl = t1 in infer (extend_list ctx (List.combine nl vl)) (Let (t, e))
          with _ -> type_fail "Not an expression of type tuple!" end
          
        | ByName (e1, n) -> infer (extend ctx (n, infer ctx e1)) (Let (t, e)))
    )
    | Apply (e1, e2) -> begin try let a = fresh_tvar () in let b = fresh_tvar () in unify (infer ctx e1) (TArrow (a,b));
        begin try unify (infer ctx e2) a; b with _ -> type_fail "Applying a function to the wrong type!" end
        with _ -> type_fail "First argument must be a function!" end

    | Var n -> begin try ctx_lookup ctx n with _ -> type_fail "Variable has no type in this context" end
    
    | Anno (e, t) -> begin try unify (infer ctx e) t; t with _ -> type_fail "Anno is incorrect!" end


(* Now you can play with the language that you've implemented! *)
let execute (s: string) : unit =
  match P.parse s with
  | Left s -> print_endline ("parsing failed: " ^ s)
  | Right e ->
     try
       (* first we type check the program *)
       ignore (infer (Ctx []) e);
       let result = eval e in
       print_endline ("program is evaluated to: " ^ Print.exp_to_string result)
     with
     | NotImplemented -> print_endline "code is not fully implemented"
     | Stuck s -> print_endline ("evaluation got stuck: " ^ s)
     | NotFound -> print_endline "variable lookup failed"
     | TypeError s -> print_endline ("type error: " ^ s)
     | e -> print_endline ("unknown failure: " ^ Printexc.to_string e)


(************************************************************
 *                     Tester template:                     *
 *         Codes to test your interpreter by yourself.      *
 *         You can change these to whatever you want.       *
 *                We won't grade these codes                *
 ************************************************************)
let list_to_string el_to_string l : string =
  List.fold_left
    begin fun acc el ->
    if acc = "" then
      el_to_string el
    else
      acc ^ "; " ^ el_to_string el
    end
    ""
    l
  |> fun str -> "[" ^ str ^ "]"

let run_test name f ts stringify : unit =
  List.iteri
    begin fun idx (input, expected_output) ->
    try
      let output = f input in
      if output <> expected_output then
        begin
          print_string (name ^ " test #" ^ string_of_int idx ^ " failed\n");
          print_string (stringify output ^ " <> " ^ stringify expected_output);
          print_newline ()
        end
    with
    | exn ->
       print_string (name ^ " test #" ^ string_of_int idx ^ " raised an exception:\n");
       print_string (Printexc.to_string exn);
       print_newline ()
    end
    ts

let run_free_vars_tests () : unit =
  run_test "free_vars" free_vars free_vars_tests (list_to_string (fun x -> x))

let run_unused_vars_tests () : unit =
  run_test "unused_vars" unused_vars unused_vars_tests (list_to_string (fun x -> x))

let run_subst_tests () : unit =
  run_test "subst" (fun (s, e) -> subst s e) subst_tests Print.exp_to_string

let run_eval_tests () : unit =
  run_test "eval" eval eval_tests Print.exp_to_string

(* You may want to change this to use the unification (unify) instead of equality (<>) *)
let run_infer_tests () : unit =
  run_test "infer" (fun (ctx, e) -> infer ctx e) infer_tests Print.typ_to_string

let run_unify_tests () : unit =
  run_test "unify" (fun (ty1, ty2) -> unify ty1 ty2) unify_tests (fun () -> "()")

let run_all_tests () : unit =
  run_free_vars_tests ();
  run_unused_vars_tests ();
  run_subst_tests ();
  run_eval_tests ();
  run_infer_tests ();
  run_unify_tests ()
;;
