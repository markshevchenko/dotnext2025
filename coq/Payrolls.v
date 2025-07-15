Require Import Arith.
Import Nat.
Require Import List.
Import ListNotations.

Definition months_in_year := 12.
(*
Рассчитывает список начислений до ноября.
count - количесто месяцев в результирующем списке.
amount - ежемесячная сумма.
result - список-аккумулятор для накопления результирующего списка.
*)
Fixpoint payrolls_till_november (count amount: nat) result :=
  match count with
  | 0 => result
  | S count' => payrolls_till_november count' amount ((months_in_year - count, amount) :: result)
  end.
  

Compute payrolls_till_november 3 1000 [].
(* = [(11, 1000); (10, 1000); (9, 1000)]
   : list (nat * nat) *)


Lemma payrolls_till_november_S (count amount: nat) (result: list (nat * nat)):
  payrolls_till_november (S count) amount result =
    payrolls_till_november count amount ((months_in_year - (S count), amount) :: result).
Proof. reflexivity. Qed.


Theorem payrolls_till_november_len (count amount: nat):
  forall result: list (nat * nat), length (payrolls_till_november count amount result) = count + length result.
Proof.
  induction count as [| count' IH]. { reflexivity. }
  intro result. rewrite payrolls_till_november_S.
  rewrite IH. simpl. apply add_succ_r.
Qed.


(*
Рассчитывает список начислений до декабря.
count - количество месяцев в результирующем списке.
month_amount - ежемесячная сумма, кроме декабрьской.
december_amount - декабрьская сумма.
*)
Definition payrolls_till_december (count month_amount december_amount: nat)
  := (months_in_year, december_amount) :: payrolls_till_november (count - 1) month_amount [].
  

Compute payrolls_till_december 4 1000 1200.
(* = [(12, 1200); (11, 1000); (10, 1000); (9, 1000)]
   : list (nat * nat) *)


(*
Создаёт частичный список начислений.
count - количество месяцев в результирующем списке.
partial-amount - частисная сумма для разбиения по месяцам.
*)
Definition make_partial_payrolls (count partial_amount: nat) :=  
  let month_amount := partial_amount / count in
  let december_amount := month_amount + partial_amount mod count in
  payrolls_till_december count month_amount december_amount.
  

Compute make_partial_payrolls 3 10000.
(* = [(12, 3334); (11, 3333); (10, 3333)]
   : list (nat * nat) *)
   
Compute make_partial_payrolls 1 10000.


(*
Рассчитывает список начислений.
month - месяц, начиная с которого составляется список.
year_amount - сумма годового начисления.
*)
Definition make_payrolls month year_amount :=
  let count := S months_in_year - month in
  let partial_amount := count * year_amount / months_in_year in
  make_partial_payrolls count partial_amount.


Compute make_payrolls 10 20000.
(* = [(12, 1668); (11, 1666); (10, 1666)]
   : list (nat * nat) *)


Definition payrolls_sum (payrolls: list (nat * nat)) :=
  list_sum (map snd payrolls).


Lemma payrolls_sum_cons (month amount: nat) (payrolls: list (nat * nat)):
  payrolls_sum ((month, amount) :: payrolls) = amount + payrolls_sum payrolls.
Proof. simpl. reflexivity. Qed.


Theorem payrolls_till_november_correct (count amount: nat):
  forall result, payrolls_sum (payrolls_till_november count amount result) = count * amount + payrolls_sum result.
Proof.
  induction count as [| count' IH]. { reflexivity. }
  intro result. rewrite payrolls_till_november_S.
  rewrite IH. rewrite payrolls_sum_cons.
  simpl. ring.
Qed.


Theorem payrolls_till_december_correct (count month_amount december_amount: nat):
  payrolls_sum (payrolls_till_december count month_amount december_amount) = december_amount + (count - 1) * month_amount.
Proof.
  unfold payrolls_till_december. rewrite payrolls_sum_cons.
  rewrite payrolls_till_november_correct.
  unfold payrolls_sum. simpl.
  rewrite add_0_r. reflexivity.
Qed.


Lemma minus_1 (count: nat): count <> 0 ->
  forall a, a + (count - 1) * a = count * a.
Proof.
  intros H a. 
  Search ((_ - _) * _). rewrite mul_sub_distr_r.
  simpl. Search (?a + 0 = ?a). rewrite add_0_r.
  Search (_ + (_ - _)). rewrite add_sub_assoc.
  2:{ Search (_ <> 0) (_ <= _). apply le_mul_l. exact H. }
  Search (_ + _ - _). rewrite add_sub_swap. 
  2:{ apply le_n. }
  Search (?x - ?x). rewrite sub_diag. reflexivity.
Qed.


Theorem make_partial_payrolls_correct (count partial_amount: nat): count <> 0 ->
  payrolls_sum (make_partial_payrolls count partial_amount) = partial_amount.
Proof.
  intro H.
  unfold make_partial_payrolls. rewrite payrolls_till_december_correct.
  rewrite add_shuffle0.
  rewrite minus_1. 2:{ assumption. }
  symmetry.
  Print div_mod.
  apply (div_mod partial_amount count).
  assumption.
Qed.


(*
Theorem make_payrolls_full_year (amount: nat):
  payrolls_sum (make_payrolls 1 amount) = amount.
Proof.
  unfold make_payrolls. unfold make_partial_payrolls.
  simpl.
  rewrite payrolls_sum_cons.
Qed.
*)