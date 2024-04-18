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
end