theory NaNoCop imports Main "HOL-Library.FSet"
begin
datatype trm
  = Var nat
  | Const nat
  | Fun nat \<open>trm list\<close>

datatype clause_elem
  = Lit bool nat \<open>trm list\<close>
  | Mat \<open>clause_elem fset fset\<close>

primrec substitute where
\<open>substitute \<sigma> (Var i) = Var (\<sigma> i)\<close> |
\<open>substitute \<sigma> (Const i) = Const i\<close> |
\<open>substitute \<sigma> (Fun i ts) = Fun i (map (substitute \<sigma>) ts)\<close>

definition 
\<open>compliment \<sigma> pol pred trms pol' pred' trms' \<equiv>
  (pol \<longleftrightarrow> \<not>pol') \<and> pred = pred' \<and> (map (substitute \<sigma>) trms  = map (substitute \<sigma>) trms')\<close>

inductive b_clause where
1: \<open>(Lit pol pred trms) |\<in>| C \<Longrightarrow> C' = C - {|(Lit pol pred trms)|} \<Longrightarrow> b_clause (pol, pred, trms) C C'\<close>|
2: \<open>
  b_clause L C' Cb \<Longrightarrow> 
  C' |\<in>| M \<Longrightarrow> 
  (Mat M) |\<in>| C \<Longrightarrow> 
  b_clause L C ((C - {|Mat M|}) |\<union>| {|Mat {|Cb|}|})\<close>

find_consts \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b fset\<close>

definition list_of_fset :: \<open>'a fset \<Rightarrow> 'a list\<close> where
  \<open>list_of_fset A \<equiv> THE l. fset_of_list l = A\<close>

primrec mat_replace where
\<open>mat_replace C C' (Lit pol pred trms) = Lit pol pred trms\<close> |
\<open>mat_replace C C' (Mat Cs) = (
  if C |\<in>| Cs
  then Mat ((Cs - {|C|}) |\<union>| {|C'|})
  else Mat (fimage (fimage (mat_replace C C')) Cs))\<close>

inductive contains_elem_in_clause where
\<open>Elem |\<in>| C \<Longrightarrow> contains_elem_in_clause Elem C\<close> |
\<open>Mat (Cs) |\<in>| C \<Longrightarrow> contains_elem_in_clause Elem C' \<Longrightarrow> C' |\<in>| Cs \<Longrightarrow> contains_elem_in_clause Elem C\<close>

inductive contains_clause_in_mat where
\<open>C |\<in>| Cs \<Longrightarrow> contains_clause_in_mat C Cs\<close> |
\<open>contains_clause_in_mat C' Cs' \<Longrightarrow> Mat Cs' |\<in>| C \<Longrightarrow> C |\<in>| Cs \<Longrightarrow> contains_clause_in_mat C' Cs\<close>

inductive contains_clause_in_clause where
\<open>C' |\<in>| M \<Longrightarrow> Mat M |\<in>| C \<Longrightarrow> contains_clause_in_clause C' C\<close> |
\<open>contains_clause_in_clause C'' C' \<Longrightarrow> C' |\<in>| M \<Longrightarrow> Mat M |\<in>| C \<Longrightarrow> contains_clause_in_clause C'' C\<close>

definition \<open>alpha_related M C pol pred trms \<equiv> 
  (\<exists> M' C1 C2. (contains_clause_in_mat {|Mat M'|} M \<or> M' = M) \<and>
  C1 |\<in>| M' \<and> C2 |\<in>| M' \<and> C1 \<noteq> C2 \<and>
  (C = C1 \<or> contains_clause_in_clause C C1) \<and>
  contains_elem_in_clause (Lit pol pred trms) C2)\<close>

fun free_vars_trm where
  \<open>free_vars_trm (Var n) = {|n|}\<close> |
  \<open>free_vars_trm (Const n) = {|n|}\<close> |
  \<open>free_vars_trm (Fun n trms) = fold (\<lambda> t s. s |\<union>| free_vars_trm t) trms {||}\<close>

definition \<open>free_vars_trms trms \<equiv> fold (\<lambda> t s. s |\<union>| free_vars_trm t) trms {||}\<close>

abbreviation \<open>contains_var_in_lit_in_clause var pol pred trms C \<equiv>
  var |\<in>| free_vars_trms trms \<and> 
  contains_elem_in_clause (Lit pol pred trms) C\<close>

definition free_vars_clause :: \<open>clause_elem fset fset \<Rightarrow> clause_elem fset \<Rightarrow> nat fset\<close> where
  \<open>free_vars_clause M C \<equiv> 
  THE vars. \<forall> var. var |\<in>| vars \<longleftrightarrow> (
    \<exists> pol pred trms. 
    contains_var_in_lit_in_clause var pol pred trms C) \<and> 
    (\<forall> pol' pred' trms' C'. 
      contains_var_in_lit_in_clause var pol' pred' trms' C' \<longrightarrow>
      contains_clause_in_mat C' M \<longrightarrow>
        (contains_clause_in_clause C' C \<or>
        C' = C \<or>
        alpha_related M C pol' pred' trms'))\<close>

definition \<open>vars_in_mat M \<equiv> THE nset. \<forall> var. var |\<in>| nset \<longleftrightarrow> (\<exists> pol pred trms C.
  var |\<in>| free_vars_trms trms \<and> Lit pol pred trms |\<in>| C \<and> contains_clause_in_mat C M)\<close>

primrec copy_term where
\<open>copy_term \<delta> (Var i) = Var (\<delta> i)\<close> |
\<open>copy_term \<delta> (Const i) = Const i\<close> |
\<open>copy_term \<delta> (Fun i trms) = Fun i (map (copy_term \<delta>) trms)\<close>

primrec copy_clause_elem where
\<open>copy_clause_elem \<delta> (Lit pol pred trms) = Lit pol pred (map (copy_term \<delta>) trms)\<close> |
\<open>copy_clause_elem \<delta> (Mat M) = Mat (fimage (fimage (copy_clause_elem \<delta>)) M)\<close>

abbreviation \<open>copy_function \<delta> M C \<equiv> \<forall> var. 
  var |\<in>| vars_in_mat {|C|} \<longrightarrow> 
  (var |\<in>| free_vars_clause M C \<longrightarrow>
  \<delta> var |\<notin>| vars_in_mat M) \<and>
  (var |\<notin>| free_vars_clause M C \<longrightarrow>
  \<delta> var = var)\<close>

definition \<open>copy_clause \<delta> M C1 C2 \<equiv> 
  copy_function \<delta> M C1 \<and>
  fimage (copy_clause_elem \<delta>) C1 = C2\<close>

fun snd_fold where
  \<open>snd_fold f (fst',snd') = (fst', fold f snd')\<close>

definition \<open>extension_clause M P C \<equiv> 
  contains_clause_in_mat C M \<and>
  ((\<exists> pol pred trms. 
    contains_elem_in_clause (Lit pol pred trms) C \<and>
    (pol,pred,trms) |\<in>| P) \<or>
  ((\<forall> pol pred trms C'. 
    (pol,pred,trms) |\<in>| P \<longrightarrow>
    contains_elem_in_clause (Lit pol pred trms) C' \<longrightarrow>
    C' |\<in>| M \<longrightarrow>
    alpha_related M C pol pred trms)) \<and>
  (C |\<notin>| M \<longrightarrow> ))\<close>

inductive CC (\<open>\<turnstile> _ _ _ _\<close> 0) where 
Axiom: \<open>\<turnstile> _ {||} _ _\<close> |
Reduction: \<open>
  (\<turnstile> \<sigma> C M (finsert (pol,pred,trms) P)) \<Longrightarrow>
  compliment \<sigma> pol pred trms pol' pred' trms' \<Longrightarrow>
  (\<turnstile> \<sigma> (finsert (Lit pol pred trms) C) M (finsert (pol,pred,trms) P))\<close> |
Extension: \<open>
  (\<turnstile> \<sigma> C M P) \<Longrightarrow>
  (\<turnstile> \<sigma> C3 (mat_replace C1 C2 M) (P |\<union>| {|(pol,pred,trms)|})) \<Longrightarrow>
  b_clause (pol,pred,trms) C2 C3 \<Longrightarrow>

  (\<turnstile> \<sigma> (C |\<union>| {|Lit pol pred trms|}) M P)\<close> |
Decomposition: \<open>
  (\<turnstile> \<sigma> (C |\<union>| C') M P) \<Longrightarrow>
  C' |\<in>| M' \<Longrightarrow>
  (\<turnstile> \<sigma> (C |\<union>| {|Mat M'|}) M P)\<close>
(*
theory NaNoCop imports Main "HOL-Library.FSet"
begin
datatype trm
  = Var nat
  | Const nat
  | Fun nat \<open>trm list\<close>

datatype clause_elem
  = Lit bool nat \<open>trm list\<close>
  | Mat \<open>clause_elem fset fset\<close>

primrec substitute where
\<open>substitute \<sigma> (Var i) = Var (\<sigma> i)\<close> |
\<open>substitute \<sigma> (Const i) = Const i\<close> |
\<open>substitute \<sigma> (Fun i ts) = Fun i (map (substitute \<sigma>) ts)\<close>

definition 
\<open>compliment \<sigma> pol pred trms pol' pred' trms' \<equiv>
  (pol \<longleftrightarrow> \<not>pol') \<and> pred = pred' \<and> (map (substitute \<sigma>) trms  = map (substitute \<sigma>) trms')\<close>

inductive b_clause where
1: \<open>
  (Lit pol pred trms) |\<in>| C \<Longrightarrow> 
  b_clause (pol, pred, trms) C (C - {|(Lit pol pred trms)|})\<close>|
2: \<open>
  b_clause L C' Cb \<Longrightarrow> 
  C' |\<in>| M \<Longrightarrow> 
  (Mat M) |\<in>| C \<Longrightarrow> 
  b_clause L C (finsert (Mat {|Cb|}) (C - {|Mat M|}))\<close>

definition list_of_fset :: \<open>'a fset \<Rightarrow> 'a list\<close> where
  \<open>list_of_fset A \<equiv> THE l. fset_of_list l = A\<close>

primrec fimage_clause where \<open>fimage_clause f (idC,C) = (idC,fimage f C)\<close>

inductive contains_elem_in_clause where
\<open>Elem |\<in>| C \<Longrightarrow> contains_elem_in_clause Elem C\<close> |
\<open>contains_elem_in_clause Elem C' \<Longrightarrow> C' |\<in>| Cs \<Longrightarrow> Mat (Cs) |\<in>| C \<Longrightarrow> 
  contains_elem_in_clause Elem C\<close>

inductive contains_clause_in_mat where
\<open>C |\<in>| Cs \<Longrightarrow> contains_clause_in_mat C Cs\<close> |
\<open>contains_clause_in_mat C' Cs' \<Longrightarrow> Mat Cs' |\<in>| C \<Longrightarrow> C |\<in>| Cs \<Longrightarrow> contains_clause_in_mat C' Cs\<close>

inductive contains_clause_in_clause where
\<open>C' |\<in>| M \<Longrightarrow> Mat M |\<in>| C \<Longrightarrow> contains_clause_in_clause C' C\<close> |
\<open>contains_clause_in_clause C'' C' \<Longrightarrow> C' |\<in>| M \<Longrightarrow> Mat M |\<in>| C \<Longrightarrow> 
  contains_clause_in_clause C'' C\<close>

primrec mat_replace where
\<open>mat_replace C C' (Lit pol pred trms) = Lit pol pred trms\<close> |
\<open>mat_replace C C' (Mat Cs) = (
  if C |\<in>| Cs 
  then Mat (finsert C' (Cs - {|C|}))
  else Mat (fimage (fimage (mat_replace C C')) Cs))\<close>


fun free_vars_trm where
  \<open>free_vars_trm (Var n) = {|n|}\<close> |
  \<open>free_vars_trm (Const n) = {|n|}\<close> |
  \<open>free_vars_trm (Fun n trms) = fold (\<lambda> t s. s |\<union>| free_vars_trm t) trms {||}\<close>

definition \<open>free_vars_trms trms \<equiv> fold (\<lambda> t s. s |\<union>| free_vars_trm t) trms {||}\<close>

abbreviation \<open>contains_var_in_lit_in_clause var pol pred trms C \<equiv>
  var |\<in>| free_vars_trms trms \<and> 
  contains_elem_in_clause (Lit pol pred trms) C\<close>

definition free_vars_clause :: \<open>clause_elem fset fset \<Rightarrow> clause_elem fset \<Rightarrow> nat fset\<close> where
  \<open>free_vars_clause M C \<equiv> 
  THE vars. \<forall> var. var |\<in>| vars \<longleftrightarrow> (
    \<exists> pol pred trms. 
    contains_var_in_lit_in_clause var pol pred trms C) \<and> 
    (\<forall> pol' pred' trms' C'. 
      contains_var_in_lit_in_clause var pol' pred' trms' C' \<longrightarrow>
      contains_clause_in_mat C' M \<longrightarrow>
        (contains_clause_in_clause C' C \<or>
        C' = C \<or>
        alpha_related M C pol' pred' trms'))\<close>

definition \<open>vars_in_mat M \<equiv> THE nset. \<forall> var. var |\<in>| nset \<longleftrightarrow> (\<exists> pol pred trms C.
  var |\<in>| free_vars_trms trms \<and> Lit pol pred trms |\<in>| C \<and> contains_clause_in_mat C M)\<close>

primrec copy_term where
\<open>copy_term \<delta> (Var i) = Var (\<delta> i)\<close> |
\<open>copy_term \<delta> (Const i) = Const i\<close> |
\<open>copy_term \<delta> (Fun i trms) = Fun i (map (copy_term \<delta>) trms)\<close>

primrec copy_clause_elem where
\<open>copy_clause_elem \<delta> (Lit pol pred trms) = Lit pol pred (map (copy_term \<delta>) trms)\<close> |
\<open>copy_clause_elem \<delta> (Mat M) = Mat (fimage (fimage (copy_clause_elem \<delta>)) M)\<close>

abbreviation \<open>copy_function \<delta> M C \<equiv> \<forall> var. 
  var |\<in>| vars_in_mat {|C|} \<longrightarrow> 
  (var |\<in>| free_vars_clause M C \<longrightarrow>
  \<delta> var |\<notin>| vars_in_mat M) \<and>
  (var |\<notin>| free_vars_clause M C \<longrightarrow>
  \<delta> var = var)\<close>

definition \<open>copy_clause \<delta> M C1 C2 \<equiv> 
  copy_function \<delta> M C1 \<and>
  fimage (copy_clause_elem \<delta>) C1 = C2\<close>

definition \<open>extension_clause M P C \<equiv> 
  contains_clause_in_mat C M \<and>
  ((\<exists> pol pred trms. 
    contains_elem_in_clause (Lit pol pred trms) C \<and>
    (pol,pred,trms) |\<in>| P) \<or>
  ((\<forall> pol pred trms C'. 
    (pol,pred,trms) |\<in>| P \<longrightarrow>
    contains_elem_in_clause (Lit pol pred trms) C' \<longrightarrow>
    C' |\<in>| M \<longrightarrow>
    alpha_related M C pol pred trms)) \<and>
  ())\<close>

inductive CC (\<open>\<turnstile> _ _ _ _\<close> 0) where 
Axiom: \<open>\<turnstile> _ {||} _ _\<close> |
Reduction: \<open>
  (\<turnstile> \<sigma> C M (finsert (pol,pred,trms) P)) \<Longrightarrow>
  compliment \<sigma> pol pred trms pol' pred' trms' \<Longrightarrow>
  (\<turnstile> \<sigma> (finsert (Lit pol pred trms) C) M (finsert (pol,pred,trms) P))\<close> |
Extension: \<open>
  (\<turnstile> \<sigma> C M P) \<Longrightarrow>
  (\<turnstile> \<sigma> C3 (mat_replace C1 C2 M) (P |\<union>| {|(pol,pred,trms)|})) \<Longrightarrow>
  b_clause (pol,pred,trms) C2 C3 \<Longrightarrow>

  (\<turnstile> \<sigma> (C |\<union>| {|Lit pol pred trms|}) M P)\<close> |
Decomposition: \<open>
  (\<turnstile> \<sigma> (C |\<union>| C') M P) \<Longrightarrow>
  C' |\<in>| M' \<Longrightarrow>
  (\<turnstile> \<sigma> (C |\<union>| {|Mat M'|}) M P)\<close>

theory NaNoCop imports Main "HOL-Library.FSet"
begin
datatype trm
  = Var nat
  | Const nat
  | Fun nat \<open>trm list\<close>

datatype clause_elem
  = Lit bool nat \<open>trm list\<close>
  | Mat \<open>(nat * clause_elem fset) fset\<close>

primrec substitute where
\<open>substitute \<sigma> (Var i) = Var (\<sigma> i)\<close> |
\<open>substitute \<sigma> (Const i) = Const i\<close> |
\<open>substitute \<sigma> (Fun i ts) = Fun i (map (substitute \<sigma>) ts)\<close>

definition 
\<open>compliment \<sigma> pol pred trms pol' pred' trms' \<equiv>
  (pol \<longleftrightarrow> \<not>pol') \<and> pred = pred' \<and> (map (substitute \<sigma>) trms  = map (substitute \<sigma>) trms')\<close>

inductive b_clause where
1: \<open>
  (Lit pol pred trms) |\<in>| C \<Longrightarrow> 
  b_clause (pol, pred, trms) (_,C) (_,C - {|(Lit pol pred trms)|})\<close>|
2: \<open>
  b_clause L C' Cb \<Longrightarrow> 
  C' |\<in>| M \<Longrightarrow> 
  (Mat M) |\<in>| C \<Longrightarrow> 
  b_clause L (_,C) (_,finsert (Mat {|Cb|}) (C - {|Mat M|}))\<close>

definition list_of_fset :: \<open>'a fset \<Rightarrow> 'a list\<close> where
  \<open>list_of_fset A \<equiv> THE l. fset_of_list l = A\<close>

primrec fimage_clause where \<open>fimage_clause f (idC,C) = (idC,fimage f C)\<close>

inductive contains_elem_in_clause where
\<open>Elem |\<in>| C \<Longrightarrow> contains_elem_in_clause Elem (_,C)\<close> |
\<open>contains_elem_in_clause Elem C' \<Longrightarrow> C' |\<in>| Cs \<Longrightarrow> Mat (Cs) |\<in>| C \<Longrightarrow> 
  contains_elem_in_clause Elem (_,C)\<close>

inductive contains_clause_in_mat where
\<open>C |\<in>| Cs \<Longrightarrow> contains_clause_in_mat C Cs\<close> |
\<open>contains_clause_in_mat C' Cs' \<Longrightarrow> Mat Cs' |\<in>| C \<Longrightarrow> (_,C) |\<in>| Cs \<Longrightarrow> contains_clause_in_mat C' Cs\<close>

inductive contains_clause_in_clause where
\<open>C' |\<in>| M \<Longrightarrow> Mat M |\<in>| C \<Longrightarrow> contains_clause_in_clause C' (_,C)\<close> |
\<open>contains_clause_in_clause C'' C' \<Longrightarrow> C' |\<in>| M \<Longrightarrow> Mat M |\<in>| C \<Longrightarrow> 
  contains_clause_in_clause C'' (_,C)\<close>

function mat_replace and clause_replace where
\<open>mat_replace C C' (Lit pol pred trms) = Lit pol pred trms\<close> |
\<open>mat_replace C C' (Mat Cs) = (
  if C |\<in>| Cs 
  then Mat (finsert C' (Cs - {|C|}))
  else Mat (fimage (clause_replace C C') Cs))\<close> |
\<open>clause_replace C C' (idC,Ms) = (idC,fimage (mat_replace C C') Ms)\<close>
  by pat_completeness auto
termination
by (relation "measure (\<lambda>(C,C,M). case M of Inl n \<Rightarrow> n | Inr n \<Rightarrow> n)") auto*)

end
end