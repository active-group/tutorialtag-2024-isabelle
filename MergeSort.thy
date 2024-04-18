theory MergeSort
  imports Main
begin

(* linorder: 'a ist eine totale Ordnung, mit \<le> *)

fun merge :: "('a :: linorder) list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
      "merge [] ys = ys"
    | "merge xs [] = xs"
    | "merge (x # xs) (y # ys) =
       (if x \<le> y 
        then x # (merge xs (y # ys))
        else y # (merge (x # xs) ys))"

fun mergesort :: "('a :: linorder) list \<Rightarrow> 'a list"
  where
    "mergesort [] = []"
  | "mergesort [x] = [x]"
  | "mergesort xs =
     (let half = (length xs) div 2
      in merge (mergesort (take half xs)) (mergesort (drop half xs)))"

(* Ist ein Element \<le> alle Elemente einer Liste? *)
fun less_equal_list :: "'a \<Rightarrow> ('a :: linorder) list \<Rightarrow> bool"
  where
    "less_equal_list x [] = True"
  | "less_equal_list x (y # ys) =
      (x \<le> y \<and> less_equal_list x ys)"
(*
     (if x \<le> y
      then less_equal_list x ys
      else False)"
*)

(* Ist Liste sortiert? *)
fun sorted :: "('a :: linorder) list \<Rightarrow> bool"
  where
    "sorted [] = True"
  | "sorted (x # xs) =
      (less_equal_list x xs \<and> sorted xs)"

(*
Induktion über induktive Daten:

Eine ist Liste eins der folgenden:
- []
- eine Cons-Liste der Form x # xs

Wenn eine Eigenschaft P für alle Listen gelten soll:
- beide Fälle abdecken
- für den Fall x # xs beweisen: P xs \<Rightarrow> P (x # xs)
*)
theorem "sorted (mergesort xs)"
  apply (induction xs rule: mergesort.induct) (* mergesort hat 3 Fälle *)
  apply (auto)
  done  

end