From Coq Require Import String Arith ZArith Psatz List.
Local Open Scope list_scope.
Import ListNotations.

(* Define some sample experession *)
Inductive expr :=
| Nat (n: nat)
| Var (x: string)
| Succ (e: expr)
| Plus (e1 e2: expr)
| Let (x: string) (e1 e2: expr)
| Seq (e1 e2: expr)
| IfZero (e1 e2 e3: expr).

Definition env := list (string * nat).

Fixpoint env_lookup (r: env) (x: string) : nat :=
  match r with
  | nil => 0
  | (y,v)::r' => if string_dec x y then v else env_lookup r' x
  end.

Fixpoint eval (e: expr) (r: env) : nat :=
  match e with 
  | Nat n => n
  | Var x => env_lookup r x
  | Succ e => S (eval e r) 
  | Plus e1 e2 => (eval e1 r) + (eval e2 r) 
  | Let x e1 e2 => 
    let v := eval e1 r in 
    eval e2((x,v)::r)
  | Seq e1 e2 => 
    let _ := eval e1 r in 
    eval e2 r
  | IfZero e1 e2 e3 => 
    match eval e1 r with 
    | O => eval e2 r 
    | _ => eval e3 r
    end
  end.

Compute eval (Nat 42) nil. (* should output: 42 *)
Compute eval (Var "x") (("x", 10)::nil). (* should output: 10 *)
Compute eval (Plus (Nat 2) (Nat 3)) nil. (* should output: 5 *)
Compute eval (Let "x" (Nat 10) (Plus (Var "x") (Nat 5))) nil. (* should output: 15 *)
Compute eval (Seq (Nat 10) (Nat 20)) nil. (* should output: 20 *)
Compute eval (IfZero (Nat 0) (Nat 10) (Nat 20)) nil. (* should output: 10 *)



