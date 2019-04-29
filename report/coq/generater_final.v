Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Lists.List.
Import ListNotations.

(* ----------------------------------------------------------------- *)
(** *** Syntax Type *)
Inductive ty : Type :=
  (* STLC *)
  | Arrow : ty -> ty -> ty
  (* numbers *)
  | Nat   : ty
  (* boolean *)
  | Bool : ty
  (* unit *)
  | Unit  : ty
  (* pairs *)
  | Prod : ty -> ty -> ty
  (* reference *)
  | Ref   : ty -> ty
  (* iterator *)
  | Itr : ty -> ty.

(* ----------------------------------------------------------------- *)
(** *** Syntax Term *)
Inductive tm : Type :=
  (* STLC *)
  | var : string -> tm
  | abs : string -> ty -> tm -> tm
  | app : tm -> tm -> tm
  (* numbers *)
  | const : nat -> tm
  | scc : tm -> tm
  | prd : tm -> tm
  | test0  : tm -> tm -> tm -> tm
  (* booleans *)
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm
  (* unit *)
  | unit : tm
  (* pairs *)
  | pair : tm -> tm -> tm
  | fst : tm -> tm
  | snd : tm -> tm
  (* sequences *)
  | seq : tm -> tm -> tm
  (* reference *)
  | ref : tm -> tm
  | deref : tm -> tm
  | assign : tm -> tm -> tm
  | loc : nat -> tm
  (* let *)
  | tlet : string -> tm -> tm -> tm
  (* fix *)
  | tfix  : tm -> tm
  (* while *)
  | twhile : tm -> tm -> tm
  (* generator *)
  | gen : tm -> tm -> tm
  | gyield : tm -> tm
  | gnext : tm -> tm.

Inductive yield_tm : tm -> Prop :=
  | Tgyield : forall t, yield_tm (gyield t).

Inductive seq_tm : tm -> Prop :=
  | Tseq : forall t1 t2, seq_tm (seq t1 t2).

(* ----------------------------------------------------------------- *)
(** *** Substitution *)
Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
  match t with
  (* STLC *)
  | var x' => if eqb_string x x' then s else t
  | app t1 t2 => app (subst x s t1) (subst x s t2)
  | abs x' T t1 => if eqb_string x x' then t else abs x' T (subst x s t1)
  (* numbers *)
  | const n => t
  | scc t1 => scc (subst x s t1)
  | prd t1 => prd (subst x s t1)
  | test0 t1 t2 t3 => test0 (subst x s t1) (subst x s t2) (subst x s t3)
  (* booleans *)
  | tru => tru
  | fls => fls
  | test t0 t1 t2 => test (subst x s t0) (subst x s t1) (subst x s t2)
  (* unit *)
  | unit => unit
  (* pairs *)
  | pair t1 t2 => pair (subst x s t1) (subst x s t2)
  | fst t => fst (subst x s t)
  | snd t => snd (subst x s t)
  (* sequences *)
  | seq t1 t2 => seq (subst x s t1) (subst x s t2)
  (* reference *)
  | ref t1 => ref (subst x s t1)
  | deref t1 => deref (subst x s t1)
  | assign t1 t2 => assign (subst x s t1) (subst x s t2)
  | loc _ => t
  (* let *)
  | tlet y t1 t2 => tlet y (subst x s t1)
    (if eqb_string x y then t2 else subst x s t2)
  (* fix *)
  | tfix t => tfix (subst x s t)
  (* while *)
  | twhile t1 t2 => twhile (subst x s t1) (subst x s t2)
  (* generator *)
  | gen t1 t2 => gen (subst x s t1) (subst x s t2)
  | gyield t => gyield (subst x s t)
  | gnext t => gnext (subst x s t)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).


(* ----------------------------------------------------------------- *)
(** *** Syntax Value *)
Inductive value : tm -> Prop :=
  (* STLC *)
  | v_abs  : forall x T t, value (abs x T t)
  (* numbers *)
  | v_nat : forall n, value (const n)
  (* booleans  *)
  | v_tru : value tru
  | v_fls : value fls
  (* unit *)
  | v_unit : value unit
  (* pair *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 -> value (pair v1 v2)
  (* reference *)
  | v_loc : forall l, value (loc l)
  (* generator *)
  | v_gyield : forall v,
      value v ->
      value (gyield v).

(* ----------------------------------------------------------------- *)
(** Reduction Help Functions and Definitions *)

(* reference *)
Definition store := list tm.
Definition store_lookup (n:nat) (st:store) := nth n st unit.

Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil    => nil
  | h :: t =>
    match n with
    | O    => x :: t
    | S n' => h :: replace n' x t
    end
  end.

(* sequence *)
(* Definition tseq t1 t2 := 
  match t1 with 
  | gyield t1' => pair t1' (abs "_" Unit t2)
  | _ => app (abs "_" Unit t2) t1
  end.
Notation "t1 ; t2" := (tseq t1 t2) (at level 80, right associativity).
Compute gyield (const 0) ; const 1 ; const 3. *)

Fixpoint seqCat (s : tm) (t : tm) : tm :=
  match s with
  | seq t1 t2 => seq t1 (seqCat t2 t)
  | t' => seq t' t
  end.
(* Compute seqCat (seq (const 0) (const 1)) (const 2).
Compute seqCat (seq (const 0) (seq (const 1) (const 2))) (const 3).
Compute (gyield (const 0)) = (const 1).
Compute not. Compute not True. Compute not False. *)


Reserved Notation "t1 '/' st1 '-->' t2 '/' st2" 
  (at level 40, st1 at level 39, t2 at level 39).

(* ----------------------------------------------------------------- *)
(** *** Reduction *)
Inductive step : tm * store -> tm * store -> Prop :=
  (* STLC *)
  | ST_AppAbs : forall x T t12 v2 st,
      value v2 ->
      app (abs x T t12) v2 / st --> [x:=v2]t12 / st
  | ST_App1 : forall t1 t1' t2 st st',
      t1 / st --> t1' / st' ->
      app t1 t2 / st --> app t1' t2 / st'
  | ST_App2 : forall v1 t2 t2' st st',
      value v1 ->
      t2 / st --> t2' / st' ->
      app v1 t2 / st --> app v1 t2'/ st'
  (* numbers *)
  | ST_SuccNat : forall n st,
      scc (const n) / st --> const (S n) / st
  | ST_Succ : forall t1 t1' st st',
      t1 / st --> t1' / st' ->
    scc t1 / st --> scc t1' / st'
  | ST_PredNat : forall n st,
      prd (const n) / st --> const (pred n) / st
  | ST_Pred : forall t1 t1' st st',
      t1 / st --> t1' / st' ->
      prd t1 / st --> prd t1' / st'
  | ST_If0 : forall t1 t1' t2 t3 st st',
      t1 / st --> t1' / st' ->
      test0 t1 t2 t3 / st --> test0 t1' t2 t3 / st'
  | ST_If0_Zero : forall t2 t3 st,
      test0 (const 0) t2 t3 / st --> t2 / st
  | ST_If0_Nonzero : forall n t2 t3 st,
      test0 (const (S n)) t2 t3 / st --> t3 / st
  (* booleans *)
  | ST_TestTrue : forall t1 t2 st,
        (test tru t1 t2) / st --> t1 / st
  | ST_TestFalse : forall t1 t2 st,
        (test fls t1 t2) / st --> t2 / st
  | ST_Test : forall t0 t0' t1 t2 st st',
       t0 / st --> t0' / st' ->
       (test t0 t1 t2) / st --> (test t0' t1 t2) / st'
  (* pairs *)
  | ST_Pair1 : forall t1 t1' t2 st st',
      t1 / st --> t1' / st' ->
      (pair t1 t2) / st --> (pair t1' t2) / st'
  | ST_Pair2 : forall v1 t2 t2' st st',
      value v1 ->
      t2 / st --> t2' / st' ->
      (pair v1 t2) / st --> (pair v1 t2') / st'
  | ST_Fst1 : forall t1 t1' st st',
      t1 / st --> t1' / st' ->
      (fst t1) / st --> (fst t1') / st'
  | ST_FstPair : forall v1 v2 st,
      value (pair v1 v2) ->
      fst (pair v1 v2) / st --> v1 / st
  | ST_Snd1 : forall t1 t1' st st',
      t1 / st --> t1' / st' ->
      (snd t1) / st --> (snd t1') / st'
  | ST_SndPair : forall v1 v2 st,
      value (pair v1 v2) ->
      snd (pair v1 v2) / st --> v2 / st
  (* sequences *)
  | ST_Seq1 : forall t1 t2 st,
      seq_tm t1 ->
      (seq t1 t2) / st --> seqCat t1 t2 / st
  | ST_Seq2 : forall t1 t1' t2 st st',
      not (seq_tm t1) ->
      t1 / st --> t1' / st' ->
      seq t1 t2 / st --> seqCat t1' t2 / st'
  | ST_Seq3 : forall v1 t2 st,
      value v1 ->
      yield_tm v1 ->
      seq v1 t2 / st --> pair v1 (abs "_" Unit t2) / st
  | ST_Seq4 : forall v1 t2 st,
      value v1 ->
      not (yield_tm v1) ->
      seq v1 t2 / st --> t2 / st
  (* reference *)
  | ST_RefValue : forall v st,
      value v ->
      ref v / st --> loc (length st) / (st ++ v::nil)
  | ST_Ref : forall t1 t1' st st',
      t1 / st --> t1' / st' ->
      ref t1 /  st --> ref t1' /  st'
  | ST_DerefLoc : forall st l,
      l < length st ->
      deref (loc l) / st --> store_lookup l st / st
  | ST_Deref : forall t1 t1' st st',
      t1 / st --> t1' / st' ->
      deref t1 / st --> deref t1' / st'
  | ST_Assign : forall v2 l st,
      value v2 ->
      l < length st ->
      assign (loc l) v2 / st --> unit / replace l v2 st
  | ST_Assign1 : forall t1 t1' t2 st st',
      t1 / st --> t1' / st' ->
      assign t1 t2 / st --> assign t1' t2 / st'
  | ST_Assign2 : forall v1 t2 t2' st st',
      value v1 ->
      t2 / st --> t2' / st' ->
      assign v1 t2 / st --> assign v1 t2' / st'
  (* let *)
  | ST_Let1 : forall x t1 t1' t2 st st',
      t1 / st --> t1'  / st' ->
      tlet x t1 t2 / st --> tlet x t1' t2 / st'
  | ST_LetValue : forall x v1 t2 st,
      value v1 ->
      tlet x v1 t2 / st --> [x:=v1]t2 / st
  (* fix *)
  | ST_Fix1 : forall t1 t1' st st',
      t1 / st --> t1' / st' ->
      tfix t1 / st --> tfix t1' / st'
  | ST_FixAbs : forall x T t st,
      tfix (abs x T t) / st --> [x:=tfix (abs x T t)]t / st
  (* while *)
  | ST_While1 : forall t1 t1' t2 st st',
      t1 / st --> t1' / st' ->
      twhile t1 t2 / st --> twhile t1' t2 / st'
  | ST_While2 : forall v1 t2 t2' st st',
      value v1 ->
      t2 / st --> t2' / st' ->
      twhile v1 t2 / st --> twhile v1 t2' / st'
  | ST_WhileFix : forall x1 T p x2 b f x st,
      twhile (abs x1 (Ref T) p) (abs x2 (Ref T) b) / st
      --> tfix (abs f (Arrow (Ref T) Unit)
               (abs x (Ref T)
               (test (app (abs x1 (Ref T) p) (var x))
                     (seq (app (abs x2 (Ref T) b) (var x))
                          (app (var f) (var x)))
                     unit))) / st
  (* generator*)
  | ST_Gen1 : forall t1 t1' t2 st st',
      t1 / st --> t1' / st' ->
      gen t1 t2 / st --> gen t1' t2 / st'
  | ST_Gen2 : forall v1 t2 t2' st st',
      value v1 ->
      t2 / st --> t2' / st' ->
      gen v1 t2 / st --> gen v1 t2' / st'
  | ST_Gen3 : forall x T g v st,
      value v ->
      gen (abs x T g) v / st --> [x:=v]g / st
  (* generator - yield *)
  | ST_Gyield : forall t t' st st',
      t / st --> t' / st' ->
      gyield t / st --> gyield t' / st'
  (* generator - next *)
  | ST_Gnext1 : forall t t' st st',
      t / st --> t' / st' ->
      gnext t / st --> gnext t' / st'
  (* generator - next - deref body function *)
  | ST_Gnext2 : forall l st,
      gnext (loc l) / st --> gnext (pair (loc l) (deref (loc l))) / st
  (* generator - next - apply body function *)
  | ST_Gnext3 : forall l t st,
      gnext (pair (loc l) (abs "_" Unit t)) / st 
      --> gnext (pair (loc l) t) / st
  (* generator - next - apply body function - (yield, rest seq)  *)
  | ST_Gnext4 : forall l t1 t2 st,
      gnext (pair (loc l) (pair (gyield t1) t2)) / st
      --> ["_":=(assign (loc l) (ref t2))]t1 / st
  (* generator - next - apply body function - (yield)*)
  | ST_Gnext5 : forall l t st,
      gnext (pair (loc l) (gyield t)) / st
      --> ["_":=(assign (loc l) unit)]t / st

where "t1 '/' st1 '-->' t2 '/' st2" := (step (t1,st1) (t2,st2)).

(* ----------------------------------------------------------------- *)
(** Typing Help Functions and Definitions *)

(* reference *)
Definition context := partial_map ty.
Definition store_ty := list ty.
Definition store_Tlookup (n:nat) (ST:store_ty) :=  nth n ST Unit.

(* ----------------------------------------------------------------- *)
(** *** Typing *)

Reserved Notation "Gamma ';' ST '|-' t '\in' T" (at level 40).

Inductive has_type : context -> store_ty -> tm -> ty -> Prop :=
  (* STLC *)
  | T_Var : forall Gamma ST x T,
      Gamma x = Some T ->
      Gamma; ST |- (var x) \in T
  | T_Abs : forall Gamma ST x T11 T12 t12,
      (update Gamma x T11); ST |- t12 \in T12 ->
      Gamma; ST |- (abs x T11 t12) \in (Arrow T11 T12)
  | T_App : forall T1 T2 Gamma ST t1 t2,
      Gamma; ST |- t1 \in (Arrow T1 T2) ->
      Gamma; ST |- t2 \in T1 ->
      Gamma; ST |- (app t1 t2) \in T2
  (* numbers *)
  | T_Nat : forall Gamma ST n,
      Gamma; ST |- (const n) \in Nat
  | T_Succ : forall Gamma ST t1,
      Gamma; ST |- t1 \in Nat ->
      Gamma; ST |- (scc t1) \in Nat
  | T_Pred : forall Gamma ST t1,
      Gamma; ST |- t1 \in Nat ->
      Gamma; ST |- (prd t1) \in Nat
  | T_If0 : forall Gamma ST t1 t2 t3 T,
      Gamma; ST |- t1 \in Nat ->
      Gamma; ST |- t2 \in T ->
      Gamma; ST |- t3 \in T ->
      Gamma; ST |- (test0 t1 t2 t3) \in T
  (* booleans *)
  | T_True : forall Gamma ST,
      Gamma; ST |- tru \in Bool
  | T_False : forall Gamma ST,
      Gamma; ST |- fls \in Bool
  | T_Test : forall Gamma ST t0 t1 t2 T,
      Gamma; ST |- t0 \in Bool ->
      Gamma; ST |-  t1 \in T ->
      Gamma; ST |-  t2 \in T ->
      Gamma; ST |-  (test t0 t1 t2) \in T
  (* unit *)
  | T_Unit : forall Gamma ST,
      Gamma; ST |- unit \in Unit
  (* pairs *)
  | T_Pair : forall Gamma ST t1 T1 t2 T2,
      Gamma; ST |- t1 \in T1 ->
      Gamma; ST |- t2 \in T2 ->
      Gamma; ST |- (pair t1 t2) \in (Prod T1 T2)
  | T_Fst : forall Gamma ST t T1 T2,
      Gamma; ST |- t \in (Prod T1 T2) ->
      Gamma; ST |- (fst t) \in T1
  | T_Snd : forall Gamma ST t T1 T2,
      Gamma; ST |- t \in (Prod T1 T2) ->
      Gamma; ST |- (snd t) \in T2
  (* sequences *)
  | T_Seq : forall Gamma ST t1 t2 T2,
      Gamma; ST |- t2 \in T2 ->
      Gamma; ST |- (seq t1 t2) \in T2
  (* reference *)
  | T_Loc : forall Gamma ST l,
      l < length ST ->
      Gamma; ST |- (loc l) \in (Ref (store_Tlookup l ST))
  | T_Ref : forall Gamma ST t1 T1,
      Gamma; ST |- t1 \in T1 ->
      Gamma; ST |- (ref t1) \in (Ref T1)
  | T_Deref : forall Gamma ST t1 T11,
      Gamma; ST |- t1 \in (Ref T11) ->
      Gamma; ST |- (deref t1) \in T11
  | T_Assign : forall Gamma ST t1 t2 T11,
      Gamma; ST |- t1 \in (Ref T11) ->
      Gamma; ST |- t2 \in T11 ->
      Gamma; ST |- (assign t1 t2) \in Unit
  (* let *)
  | T_Let : forall Gamma ST x t1 T1 t2 T2,
      Gamma; ST |- t1 \in T1 ->
      (update Gamma x T1); ST |- t2 \in T2 ->
      Gamma; ST |- (tlet x t1 t2) \in T2
  (* fix *)
  | T_Fix : forall Gamma ST t1 T1 T2,
      Gamma; ST |- t1 \in (Arrow T1 T2) ->
      Gamma; ST |- (tfix t1) \in T2
  (* while *)
  | T_While : forall Gamma ST t1 t2 T,
      Gamma; ST |- t1 \in (Arrow T Bool) ->
      Gamma; ST |- t2 \in (Arrow T T) ->
      Gamma; ST |- twhile t1 t2 \in T
  (* generator*)
  | T_Gen : forall Gamma ST t1 t2 T1 T2,
      Gamma; ST |- t1 \in (Arrow T1 (Ref (Arrow Unit T2))) ->
      Gamma; ST |- t2 \in T1 ->
      Gamma; ST |- gen t1 t2 \in Ref (Itr T1)
  | T_Gyield : forall Gamma ST t T,
      Gamma; ST |- t \in T ->
      Gamma; ST |- gyield t \in T
  | T_Gnext : forall Gamma ST t T,
      Gamma; ST |- t \in Ref (Itr T) ->
      Gamma; ST |- gnext t \in T

where "Gamma ';' ST '|-' t '\in' T" := (has_type Gamma ST t T).