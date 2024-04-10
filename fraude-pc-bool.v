(* *)

From Coq Require Import String Arith ZArith Psatz List.

Local Open Scope list_scope.
Import ListNotations.


Definition id := string.

Inductive expr : Type :=
| Nat (n : nat)
| Bool (b : bool) (* NEW *)
| Var (x : id)
| Succ (e : expr)
| Plus (e1 e2 : expr)
| Let (x : id) (e1 e2 : expr)
| IfZero (e1 e2 e3 : expr).


Example e1 := (Let "x"%string (Nat 5) (Var "x"%string)) : expr.

(* Fraude semantics via interpreter *)

(* NEW *)
(* Values include booleans and nats now *)
Inductive val : Type :=
| VNat (n : nat)
| VBool (b : bool).

Definition env : Type := list (id * val). (* NEW: maps to val now *)

Fixpoint env_lookup (r : env) (x : id) :=
  match r with
  | nil => VNat 99 (* whatevs *)
  | (y, v) :: r =>
      if String.eqb x y then v else env_lookup r x
  end.

(* With the introduction of Booleans, we now have the possibility of
   run-time errors when evaluating expressions like (Succ (Bool true)).
   We model this possibility as an option val result type for eval.
   If an expression produces a run-time error, the result is None.
   Otherwise it is Some val. *)

(* NEW: produces an option val *)
Fixpoint eval (e : expr) (r : env) : option val :=
  match e with
  | Nat n => Some (VNat n)
  | Bool b => Some (VBool b)
  | Var x => Some (env_lookup r x)
  | Succ e =>
      match eval e r with
      | Some (VNat n) => Some (VNat (S n))
      | _ => None
      end
  | Plus e1 e2 =>
      match eval e1 r with
      | Some (VNat n1) =>
          match eval e2 r with
          | Some (VNat n2) =>
              Some (VNat (n1 + n2))
          | _ => None
          end
      | _ => None
      end
  | Let x e1 e2 =>
      match eval e1 r with
      | Some v => eval e2 ((x, v) :: r)
      | _ => None
      end
  | IfZero e1 e2 e3 =>      
      match eval e1 r with
      | Some (VNat 0) => eval e2 r
      | Some _ => eval e3 r
      | _ => None
      end
  end.

(* These are some potentially helpful lemmas for doing inversion
   on evaluation. *)

Lemma eval_succ_inv : forall e r v,
    eval (Succ e) r = Some v ->
    exists n, v = VNat (S n) /\ eval e r = Some (VNat n).
Proof.
  intros.
  simpl in H.
  destruct (eval e r) as [[|] |];
  try discriminate.
  injection H. 
  eauto.
Qed.

Lemma eval_plus_inv : forall e1 e2 r v,
    eval (Plus e1 e2) r = Some v ->
    exists n1,
    exists n2,
      v = VNat (n1 + n2) /\
        eval e1 r = Some (VNat n1) /\
        eval e2 r = Some (VNat n2).
Proof.
  simpl.
  intros e1 e2 r v H.
  destruct (eval e1 r) as [[|] |]; try discriminate.
  destruct (eval e2 r) as [[|] |]; try discriminate.
  injection H. eauto.
Qed.

Lemma eval_let_inv : forall x e1 e2 r v,
    eval (Let x e1 e2) r = Some v ->
    exists v',
      eval e1 r = Some v' /\
        eval e2 ((x,v')::r) = Some v.
Proof.
  simpl.
  intros x e1 e2 r v H.
  destruct (eval e1 r); try discriminate.
  eauto.
Qed.

Lemma eval_ifz_inv : forall e1 e2 e3 r v,
    eval (IfZero e1 e2 e3) r = Some v ->
    exists v',     
      eval e1 r = Some v' /\
        (v' = VNat 0 -> eval e2 r = Some v) /\
        (v' <> VNat 0 -> eval e3 r = Some v).
Proof.
  intros e1 e2 e3 r v H.
  simpl in H.
  destruct (eval e1 r); try discriminate.
  - eexists.
    split.
    + eauto.
    + destruct v0.
      * split.
        { intros. inversion H0. subst n. auto. }
        { intros. destruct n. 
          { contradiction. }
          { auto. }}
      * split.
        { intros.  inversion H0. }
        { intros. auto. }
Qed.

(* Machine semantics *)

Module Reg.
  Record rs : Type :=
    R { rax : nat 
      ; rbx : nat
      ; ZF : bool }.
End Reg.

Inductive reg :=
| rax
| rbx.

Inductive instr : Type :=
| Mov (r : reg) (n : nat)
| Push (r : reg)
| Pop (r : reg)
| Addi (r : reg) (n : nat)
| Addr (r1 r2 : reg)
| StackRef (r : reg) (n : nat)
| Cmpi (r : reg) (n : nat)
| Je (i : nat)     
| JmpFwd (i : nat)
| JmpBck (i : nat)
| Halt.

Definition asm : Type := list instr.

Definition set_register (r : reg) (rs : Reg.rs) (n : nat) : Reg.rs :=
  match r with
  | rax => {| Reg.rax := n; Reg.rbx := Reg.rbx rs; Reg.ZF := Reg.ZF rs |}
  | rbx => {| Reg.rbx := n; Reg.rax := Reg.rax rs; Reg.ZF := Reg.ZF rs |}
  end.

Definition get_register (r : reg) (rs : Reg.rs) : nat :=
  match r with
  | rax => Reg.rax rs
  | rbx => Reg.rbx rs
  end.

Definition set_zf (rs : Reg.rs) (b : bool) : Reg.rs :=
  {| Reg.ZF := b
  ;  Reg.rax := Reg.rax rs
  ;  Reg.rbx := Reg.rbx rs |}.

Definition stack : Type := list nat.

Definition config : Type := (nat * stack * Reg.rs)%type.

Fixpoint instr_at (p : asm) (pc : nat) : option instr :=
  match p with
  | nil => None
  | i :: p' => if pc =? 0 then Some i else instr_at p' (pc - 1)
  end.

Inductive transition (p : asm) : config -> config -> Prop :=
| trans_mov : forall pc s rs rs' r n,
    instr_at p pc = Some (Mov r n) ->
    rs' = set_register r rs n ->
    transition p
      (pc, s, rs)
      (pc + 1, s, rs')
| trans_push : forall pc s rs r,
    instr_at p pc = Some (Push r) ->
    transition p
      (pc, s, rs)
      (pc + 1, get_register r rs :: s, rs)
| trans_pop : forall pc s rs rs' r n,
    instr_at p pc = Some (Pop r) ->
    rs' = set_register r rs n ->
    transition p
      (pc, n :: s, rs)
      (pc + 1, s, rs')
| trans_addi : forall pc s rs rs' r n,
    instr_at p pc = Some (Addi r n) ->
    rs' = set_register r rs (n + (get_register r rs)) ->
    transition p
      (pc, s, rs)
      (pc + 1, s, rs')
| trans_addr : forall pc s rs rs' r1 r2,
    instr_at p pc = Some (Addr r1 r2) ->
    rs' = set_register r1 rs ((get_register r2 rs) + (get_register r1 rs)) ->
    transition p
      (pc, s, rs)
      (pc + 1, s, rs')
| trans_stackref : forall pc s rs rs' r n,
    instr_at p pc = Some (StackRef r n) ->
    rs' = set_register r rs (nth n s 0) ->
    transition p
      (pc, s, rs)
      (pc + 1, s, rs')
| trans_cmp : forall pc s rs r n,
    instr_at p pc = Some (Cmpi r n) ->
    transition p
      (pc, s, rs)
      (pc + 1, s, set_zf rs (Nat.eqb n (get_register r rs)))
| trans_je : forall pc s rs i,
    instr_at p pc = Some (Je i) ->    
    transition p
      (pc, s, rs)
      (pc + 1 + (if (Reg.ZF rs) then i else 0), s, rs)
| trans_jmpfwd : forall pc s rs n,
    instr_at p pc = Some (JmpFwd n) ->
    transition p
      (pc, s, rs)
      (pc + 1 + n, s, rs)
| trans_jmpbck : forall pc s rs n,
    instr_at p pc = Some (JmpBck n) ->
    transition p
      (pc, s, rs)
      (pc - n, s, rs).

Inductive transitions (p : asm) : config -> config -> Prop :=
| trans_refl : forall c, transitions p c c
| trans_step : forall c1 c2 c3,
    transition p c1 c2 ->
    transitions p c2 c3 ->
    transitions p c1 c3.

Lemma trans_one : forall (p : asm) c1 c2,
    transition p c1 c2 ->
    transitions p c1 c2.
Proof.
  intros.
  eapply trans_step.
  - eauto.
  - constructor.
Qed.

Lemma trans_trans :
  forall p c1 c2, transitions p c1 c2 ->
                  forall c3, transitions p c2 c3 ->
                             transitions p c1 c3.
Proof.
  intros p c1 c2 H.
  induction H; intros.
  - auto.
  - apply IHtransitions in H1.
    econstructor; eauto.
Qed.

Definition rs0 := {| Reg.rax := 0; Reg.rbx := 0; Reg.ZF := false |}.

Definition machine_terminates (p : asm) (n : nat) : Prop :=
  exists pc rs, transitions p (0, [], rs0) (pc, [], rs)
                /\ Reg.rax rs = n
                /\ instr_at p pc = Some Halt.

(* Compiler *)

Definition cenv : Type := list (option id).

Fixpoint cenv_lookup (r : cenv) (x : id) : nat :=
  match r with
  | [] => 0
  | (Some y) :: r =>
      if String.eqb x y then 0 else S (cenv_lookup r x)
  | None :: r =>
      S (cenv_lookup r x)
  end.

Definition nat_to_bits (n : nat) : nat :=
  Nat.double n.

Definition bool_to_bits (b : bool) : nat :=
  match b with
  | true => 1
  | false => 3
  end.

Definition val_to_bits (v : val) : nat :=
  match v with
  | VBool true => 1
  | VBool false => 3
  | VNat n => Nat.double n
  end.

Definition bits_to_val (n : nat) : option val :=
  if (Nat.even n)
  then Some (VNat (Nat.div2 n))
  else
    match n with       
    | 1 => Some (VBool true)
    | 3 => Some (VBool false)
    | _ => None
    end.

Lemma dbl_even : forall n,
    Nat.even (Nat.double n) = true.
Proof.
  induction n.
  - auto.
  - unfold Nat.double.
    replace (S n + S n) with (S (S (Nat.double n))).
    + simpl. auto.
    + unfold Nat.double. lia.
Qed.

Lemma dbl_half : forall n,
    Nat.div2 (Nat.double n) = n.
Proof.
  intros.
  replace (Nat.double n) with (2 * n).
  - rewrite Nat.div2_double. auto.
  - unfold Nat.double. lia.
Qed.


Lemma val_to_val : forall v,
    bits_to_val (val_to_bits v) = Some v.
Proof.
  intros.
  destruct v.
  - simpl. unfold bits_to_val.
    rewrite dbl_even.
    rewrite dbl_half. auto.
  - simpl. destruct b; auto.
Qed.


Fixpoint compile (e : expr) (r : cenv) : asm :=
  match e with
  | Nat n => [ Mov rax (nat_to_bits n) ]
  | Bool b => [ Mov rax (bool_to_bits b) ]               
  | Var x => [ StackRef rax (cenv_lookup r x) ]
  | Succ e =>
      compile e r
        ++ [ Addi rax 2 ]
  | Plus e1 e2 =>
      compile e1 r
        ++ [ Push rax ]
        ++ compile e2 (None :: r)
        ++ [ Pop rbx; Addr rax rbx ]
  | Let x e1 e2 =>
      compile e1 r
        ++ [ Push rax ]
        ++ compile e2 (Some x :: r)
        ++ [ Pop rbx ]
  | IfZero e1 e2 e3 =>
      compile e1 r
        ++ [ Cmpi rax 0 ;
             Je (length (compile e3 r) + 1) ]
        ++ compile e3 r
        ++ [ JmpFwd (length (compile e2 r)) ]
        ++ compile e2 r
  end.

(* Compiler correctness *)

Inductive related : stack -> cenv -> env -> Prop :=
| related_mt : related [] [] []
| related_cons
    (s : stack) (c : cenv) (r : env) (x : id) (v : val):
  related s c r ->
  related (val_to_bits v :: s) (Some x :: c) ((x,v) :: r)
| related_push (s : stack) (c : cenv) (r : env) (v : val):
  related s c r ->
  related (val_to_bits v :: s) (None :: c) r.

Inductive closes : cenv -> expr -> Prop :=
| closes_nat (c : cenv) (n : nat) : closes c (Nat n)
| closes_bool (c : cenv) (b : bool) : closes c (Bool b)
| closes_var (c : cenv) (x : id) :
  In (Some x) c ->
  closes c (Var x)
| closes_succ (c : cenv) (e : expr) :
  closes c e ->
  closes c (Succ e)
| closes_plus (c : cenv) (e1 e2 : expr) :
  closes c e1 ->
  closes c e2 ->
  closes c (Plus e1 e2)
| closes_let (c : cenv) (e1 e2 : expr) (x : id) :
  closes c e1 ->
  closes (Some x :: c) e2 ->
  closes c (Let x e1 e2)
| close_ifz (c : cenv) (e1 e2 e3 : expr) :
  closes c e1 ->
  closes c e2 ->
  closes c e3 ->
  closes c (IfZero e1 e2 e3).

Definition subset (c1 c2 : cenv) :=
  forall x,
    In x c1 -> In x c2.

Lemma weaken : forall (e : expr) (c1 c2 : cenv),
    closes c1 e ->
    subset c1 c2 ->
    closes c2 e.
Proof.
  induction e; intros ; constructor; inversion H; eauto.
  eapply IHe2; eauto.
  unfold subset.
  intros x1 []; subst.
  - left. auto.
  - right. auto.
Qed.

Lemma closes_none : forall (e : expr) (c : cenv),
    closes c e ->
    closes (None :: c) e.
Proof.
  intros.
  eapply weaken.
  - eauto.
  - unfold subset. destruct x; intros.
    * right. auto.
    * left. auto.
Qed.

Lemma lookup_in_related_envs :
  forall (c : cenv) (s : stack) (r : env) (d : nat) (x : id),
    related s c r ->
    In (Some x) c ->
    nth (cenv_lookup c x) s d = val_to_bits (env_lookup r x).
Proof.
  induction c; intros.
  - inversion H0.
  - inversion H. subst. simpl. destruct (String.eqb x x0) eqn:E.
    + auto.
    + inversion H. apply IHc; auto.
      simpl in H0. destruct H0 as [[= Hm] | Hb].
      * subst x0.
        rewrite eqb_refl in E.
        discriminate E.
      * auto.
    + apply IHc.
      * apply H5.
      * subst. simpl in H0.
        destruct H0 as [[=] | H2]; auto.
Qed.

Inductive code_at: asm -> nat -> asm -> Prop :=
| code_at_intro: forall p1 p2 p3 pc,
    pc = length p1 ->
    code_at (p1 ++ p2 ++ p3) pc p2.

Lemma instr_at_app:
  forall i p2 p1 pc,
  pc = length p1 ->
  instr_at (p1 ++ i :: p2) pc = Some i.
Proof.
  induction p1; simpl; intros; subst pc.
  - auto.
  - assert (A: S (length p1) =? 0 = false).
    { apply Nat.eqb_neq. lia. }
    rewrite A.
    replace (S (length p1) - 1) with (length p1).
    eapply IHp1.
    + auto.
    + lia.
Qed.

Lemma code_at_head:  
  forall p pc i p',
    code_at p pc (i :: p') ->
    instr_at p pc = Some i.
Proof.
  intros. inversion H. simpl. apply instr_at_app. auto.
Qed.

Lemma code_at_tail:
  forall p pc i p',
    code_at p pc (i :: p') ->
    code_at p (pc + 1) p'.
Proof.
  intros. inversion H.
  change (p1 ++ (i :: p') ++ p3)
    with (p1 ++ (i :: nil) ++ p' ++ p3).
  rewrite <- app_ass. constructor. rewrite app_length. subst pc. auto.
Qed.

Lemma code_at_app_left:
  forall p pc p1 p2,
  code_at p pc (p1 ++ p2) ->
  code_at p pc p1.
Proof.
  intros. inversion H. rewrite app_ass. constructor. auto.
Qed.

Lemma code_at_app_right:
  forall p pc p1 p2,
  code_at p pc (p1 ++ p2) ->
  code_at p (pc + length p1) p2.
Proof.
  intros. inversion H. rewrite app_ass. rewrite <- app_ass.
  constructor. subst pc. symmetry. apply app_length.
Qed.

Lemma code_at_app_right2:
  forall p pc p1 p2 p3,
  code_at p pc (p1 ++ p2 ++ p3) ->
  code_at p (pc + length p1) p2.
Proof.
  intros. apply code_at_app_right.
  apply code_at_app_left with (p2:=p3).
  rewrite app_ass; auto.
Qed.

Lemma code_at_nil:
  forall p pc p1,
    code_at p pc p1 ->
    code_at p pc [].
Proof.
  intros. inversion H. subst.
  change (p1 ++ p3) with ([] ++ p1 ++ p3).
  constructor. auto.
Qed.

Lemma instr_at_code_at_nil:
  forall p pc i,
    instr_at p pc = Some i ->
    code_at p pc nil.
Proof.
  induction p; simpl; intros.
  - discriminate.
  - destruct (pc =? 0) eqn:PC.
    + assert (pc = 0) by (apply Nat.eqb_eq; auto).
      subst pc.
      change (a :: p) with ([] ++ [] ++ (a :: p)).
      constructor. auto.
    + assert (A: code_at p (pc - 1) []) by eauto.
      inversion A; subst.
      apply code_at_intro with (p1:=a::p1) (p3:=p3).
      simpl. rewrite <- H0.
      destruct pc.
      * discriminate.
      * lia.
Qed.


Definition ifz (v : val) : bool :=
  match v with
  | VNat 0 => true
  | _ => false
  end.

Lemma ifz_true:
  forall v,
    ifz v = true -> v = VNat 0.
Proof.
  intros. destruct v.
  - destruct n.
    + auto.
    + discriminate.
  - discriminate.
Qed.

Lemma ifz_false:
  forall v,    
    ifz v = false ->
    v <> VNat 0 /\
    exists n, val_to_bits v = S n.
Proof.
  intros. destruct v.
  - destruct n.
    + discriminate.
    + split.
      * unfold not. intros. discriminate.
      * simpl.
       unfold Nat.double.
       eexists. eauto.
  - split.
    + unfold not. intros. discriminate.
    + simpl. eexists (if b then 0 else 2).
      destruct b; auto.
Qed.


Hint Resolve code_at_head code_at_tail code_at_app_left code_at_app_right
  code_at_app_right2 code_at_nil instr_at_code_at_nil: code.

Hint Rewrite app_length Nat.add_assoc Nat.add_0_r : code.

Lemma compiler_expr_correct :
  forall e s r c rs p pc v,
    code_at p pc (compile e c) ->
    related s c r ->
    closes c e ->
    eval e r = Some v ->
    (exists rs',
        Reg.rax rs' = val_to_bits v /\
        transitions p
          (pc, s, rs)
          (pc + length (compile e c), s, rs')).

Proof.
  induction e; simpl; intros.

  - (* Nat *)
    exists (set_register rax rs (val_to_bits v)); split; auto.
    apply trans_one.
    apply code_at_head in H.
    apply trans_mov with rax (nat_to_bits n); auto.
    injection H2 as Hnv.
    rewrite <- Hnv.
    auto.
    - (* Bool *)
    exists (set_register rax rs (val_to_bits v)); split; auto.
    apply trans_one.
    apply code_at_head in H.
    apply trans_mov with rax (bool_to_bits b); auto.
    injection H2 as Hbv.
    rewrite <- Hbv.
    auto.
  - exists (set_register rax rs (val_to_bits v)); split; auto.
    apply trans_one.
    apply code_at_head in H.
    apply trans_stackref with rax (cenv_lookup c x); auto.
    injection H2 as Hbv.
    assert (nth (cenv_lookup c x) s 0 = val_to_bits v).
    rewrite <- Hbv.
    apply lookup_in_related_envs; auto.
    + inversion H1.
      auto.
    + rewrite H2.
      reflexivity.
  - remember (eval e r) as res.
    induction res; try discriminate.
    induction a; try discriminate.
    injection H2 as H2.
    destruct IHe with s r c rs p pc (VNat n) as (rs', Hrs'); auto.
    + inversion H.
      rewrite <- app_assoc.
      apply code_at_intro.
      auto.
    + inversion H1.
      auto.
    + exists (set_register rax rs' (val_to_bits v)); split; auto.
      destruct Hrs'.
      rewrite app_length, Nat.add_assoc.
      apply trans_trans with (pc + length (compile e c), s, rs'); auto.
      apply trans_one.
      apply trans_addi with rax 2.
      * apply code_at_app_right in H.
        apply code_at_head in H.
        auto.
      * rewrite <- H2.
        simpl.
        rewrite H3, Nat.double_S.
        auto.

      
  - (* Plus e2 e3 *)
    simpl in H; inversion H1.
    replace (pc + length (compile e2 c ++ Push rax :: compile e3 (None :: c) ++ [Pop rbx; Addr rax rbx]))
      with (pc + length (compile e2 c) + 1 + length (compile e3 (None :: c)) + 1 + 1).

    + apply eval_plus_inv in H2 as [n1 [n2 [Hv [He1 He2]]]]. subst v.
      eapply IHe1 with (v:=VNat n1) in H6 as [rs1 [Ha Hb]].
      * eapply closes_none in H7.
        eapply IHe2 with (v:=VNat n2) in H7 as [rs2 [Hc Hd]].
        { eexists {| Reg.rax := _ |}. split.
          { simpl. eauto. }
          { eapply trans_trans.
            { eapply Hb. }
            { eapply trans_trans.
              { eapply trans_one.
                eapply trans_push.
                eauto with code. }
              { eapply trans_trans.
                { eapply Hd. }
                { eapply trans_trans.
                  { eapply trans_one.
                    eapply trans_pop.
                    { eauto with code. }
                    { eauto. }}
                  { eapply trans_trans.
                    { eapply trans_one.
                      eapply trans_addr.
                      { eauto 6 with code. }
                      { eauto. }
                    }
                    { 
                      simpl. rewrite Hc. rewrite Ha. simpl.
                      unfold Nat.double.
                      replace (n1 + n1 + (n2 + n2)) with (n1 + n2 + (n1 + n2)) by lia.
                      eapply trans_refl.
                     }
                   }
                 }
               }
             }
           }
        }

        { eauto with code. }
        { simpl. rewrite Ha. apply related_push. eauto. }
        { auto. }
      * eauto with code.
      * eauto.
      * auto.
    + repeat (rewrite app_length; simpl). lia.
 
  - (* Let x e2 e3 *)
    simpl in H; inversion H1.
    apply eval_let_inv in H2 as [v' [He1 He2]].
    replace (pc + length (compile e2 c ++ Push rax :: compile e3 (Some x :: c) ++ [Pop rbx])) with
      (pc + length (compile e2 c) + 1 + length (compile e3 (Some x :: c)) + 1).
    
    + eapply IHe1 with (v:=v') in H6 as [rs1 [Ha Hb]].
      * eapply IHe2 in H8 as [rs2 [Hc Hd]].
        { eexists {| Reg.rax := _ |}. split.
          { simpl. eauto. }
          { eapply trans_trans.
            { eapply Hb. }
            { eapply trans_trans.
              { eapply trans_one.
                eapply trans_push.
                eauto with code. }
              { eapply trans_trans.
                { eapply Hd. }
                { eapply trans_one. simpl.
                  eapply trans_pop.
                  { eauto with code. }
                  { simpl. eauto. }}}}}}
        { eauto with code. }
        { simpl. rewrite Ha. apply related_cons. eauto. }
        { auto. }
        
      * eauto with code.
      * eauto.
      * auto.
    + repeat (rewrite app_length; simpl). lia.
  
  - (* IfZero e2 e3 e4 *)
      simpl in H; inversion H1.
      apply eval_ifz_inv in H2 as [v' [He1 [HeT HeF]]].
    
    replace (pc + length (compile e2 c ++ Cmpi rax 0 :: Je (length (compile e4 c) + 1)
                            :: compile e4 c ++ JmpFwd (length (compile e3 c))
                            :: compile e3 c))
      with (pc + length (compile e2 c) + 1 + 1 +
              (length (compile e4 c) + 1) +
              length (compile e3 c)).

    + eapply IHe1 with (r:=r) (v:=v') in H7 as [rs1 [Ha Hb]].
      { destruct (ifz v') eqn:E.
        { apply ifz_true in E. subst v'.
          eapply IHe2 with (r:=r) (rs:=set_zf rs1 true)
            in H8 as [rs2 [Hc Hd]].
          { exists rs2. split.
            { eauto. }
            { eapply trans_trans.
              { eapply Hb. }
              { eapply trans_trans.
                { eapply trans_one.
                  eapply trans_cmp.
                  eauto with code. }
                { eapply trans_trans.
                  { eapply trans_one.
                    eapply trans_je.
                    eauto with code. }
                  { simpl. rewrite Ha. simpl. apply Hd. }}}}}
          { autorewrite with code. eauto 6 with code. }
          { auto. }
          { auto. }}
        { apply ifz_false in E as [Hv' [n' Hn']].
          eapply IHe3 with (r:=r) (rs:=set_zf rs1 false)
            in H9 as [rs3 [He Hf]].
          { exists rs3. split.
            { eauto. }
            { eapply trans_trans.
              { eapply Hb. }
              { eapply trans_trans.
                { eapply trans_one.
                  eapply trans_cmp.
                  eauto with code. }
                { eapply trans_trans.
                  { eapply trans_one.
                    eapply trans_je.
                    eauto with code. }
                  { simpl. rewrite Ha. rewrite Hn'.
                    eapply trans_trans.
                    { eauto with code. }
                    { eapply trans_one.
                      rewrite Nat.add_0_r.
                      rewrite Nat.add_assoc.
                      eapply trans_jmpfwd.
                      eauto 6 with code. }
                    }
                 }
              }
            }
          }
          { autorewrite with code. eauto with code. }
          { auto. }
          { auto. }
        }
      }
      { autorewrite with code. eauto with code. }
      { auto. }
      { auto. }
    + repeat (rewrite app_length; simpl). lia.
    
Qed.

Theorem compiler_correctness : forall (e : expr) (v : val),
    closes [] e ->
    eval e [] = Some v ->
    machine_terminates (compile e [] ++ [ Halt ]) (val_to_bits v).
Proof.
  intros. 
  eapply compiler_expr_correct in H as [rs' [Ha Hb]].
  - unfold machine_terminates.
    exists (0 + length (compile e [])).
    exists rs'.
    split.
    + eapply Hb.
    + erewrite Ha.
      split.
      * eauto.
      * eapply code_at_head.
        apply code_at_intro with (p2:=[Halt]).
        lia.
  - apply code_at_intro with (p1:=[]). auto.
  - constructor.
  - auto.
Qed.
