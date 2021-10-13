theory NaNoCop imports Main
begin

(*----------FSET-----------*)
datatype 'a fset 
  = Empty (\<open>\<lbrace>\<rbrace>\<close>)
  | Insert 'a \<open>'a fset\<close>

primrec fset_to_set where
  \<open>fset_to_set Empty = {}\<close> |
  \<open>fset_to_set (Insert x xs) = insert x (fset_to_set xs)\<close>

lemma fset_is_finite: \<open>finite (fset_to_set xs)\<close> 
  by (induct xs) auto

primrec fmember (infix\<open>|\<in>|\<close> 200) where
  \<open>(_ |\<in>| Empty) = False\<close> |
  \<open>(x |\<in>| Insert x' xs) = ((x = x') \<or> (x |\<in>| xs))\<close>

lemma fmember_is_member[simp]: \<open>x |\<in>| xs \<longleftrightarrow> x \<in> (fset_to_set xs)\<close> 
  by (induct xs) simp_all

abbreviation fnotmember (infix \<open>|\<notin>|\<close> 200) where \<open>x |\<notin>| xs \<equiv> \<not> x |\<in>| xs\<close>

definition \<open>finsert x xs \<equiv> (if (x |\<in>| xs) then xs else Insert x xs)\<close>

lemma finsert_is_insert: \<open>fset_to_set (finsert x xs) = insert x (fset_to_set xs)\<close>
  by (induct xs) (simp_all add: finsert_def insert_absorb)

syntax
  "_insert_fset"     :: "args => 'a fset"  ("\<lbrace>(_)\<rbrace>")

translations
  "\<lbrace>x, xs\<rbrace>" == "CONST finsert x \<lbrace>xs\<rbrace>"
  "\<lbrace>x\<rbrace>"     == "CONST finsert x \<lbrace>\<rbrace>"

primrec fsubseteq (infix \<open>|\<subseteq>|\<close> 120) where
  \<open>(Empty |\<subseteq>| _) = True\<close> |
  \<open>(Insert x xs |\<subseteq>| ys) = ((x |\<in>| ys) \<and> (xs |\<subseteq>| ys))\<close>

lemma fsubseteq_is_subseteq[simp]: \<open>xs |\<subseteq>| ys \<longleftrightarrow> (fset_to_set xs) \<subseteq> (fset_to_set ys)\<close> 
  by (induct xs) simp_all

primrec fremove where
  \<open>fremove _ \<lbrace>\<rbrace> = \<lbrace>\<rbrace>\<close> |
  \<open>fremove x (Insert y ys) = (if y = x then fremove x ys else Insert y (fremove x ys))\<close>

lemma fremove_is_remove: \<open>fset_to_set (fremove x xs) = (fset_to_set xs) - {x}\<close>
  by (induct xs) (simp_all add: insert_Diff_if)
  
primrec fminus (infix \<open>|-|\<close> 210) where
  \<open>xs |-| \<lbrace>\<rbrace> = xs\<close> |
  \<open>xs |-| (Insert y ys) = (fremove y xs) |-| ys\<close>

lemma hoist_fremove:\<open>fset_to_set ((fremove x xs) |-| ys) = fset_to_set (fremove x (xs |-| ys))\<close> 
  apply (induct ys arbitrary: x xs)
   apply simp
  by (metis Diff_insert Diff_insert2 fminus.simps(2) fremove_is_remove)

lemma fminus_is_minus[simp]: \<open>fset_to_set (xs |-| ys) = (fset_to_set xs) - (fset_to_set ys)\<close>
proof (induct ys)
  case Empty
  then show ?case by simp
next
  case (Insert y ys)
  have \<open>fset_to_set (xs |-| Insert y ys) = fset_to_set (xs |-| ys) - {y}\<close>
    by (simp add: hoist_fremove fremove_is_remove)
  then show ?case
    using Insert.hyps by force
qed

definition fequal (infix \<open>|=|\<close> 120) where \<open>xs |=| ys \<equiv> xs |\<subseteq>| ys \<and> ys |\<subseteq>| xs\<close>

lemma fequal_is_equal[simp]: \<open>xs |=| ys \<longleftrightarrow> (fset_to_set xs) = (fset_to_set ys)\<close>
  by (simp add: fequal_def set_eq_subset)

primrec fimage where
  \<open>fimage f \<lbrace>\<rbrace> = \<lbrace>\<rbrace>\<close> |
  \<open>fimage f (Insert x xs) = Insert (f x) (fimage f xs)\<close>

lemma fimage_is_image[simp]: \<open>fset_to_set (fimage f xs) = image f (fset_to_set xs)\<close>
  by (induct xs) simp_all

primrec funion (infix \<open>|\<union>|\<close> 110) where
  \<open>funion xs \<lbrace>\<rbrace> = xs\<close> |
  \<open>funion xs (Insert y ys) = (if y |\<in>| xs then funion xs ys else Insert y (funion xs ys))\<close>

lemma funion_is_union[simp]: \<open>fset_to_set (xs |\<union>| ys) = fset_to_set xs \<union> fset_to_set ys\<close> 
  by (induct ys) auto

primrec isfset where
  \<open>isfset \<lbrace>\<rbrace> = True\<close> |
  \<open>isfset (Insert x xs) = (x |\<notin>| xs \<and> isfset xs)\<close>

primrec ffold where
  \<open>ffold f \<lbrace>\<rbrace> s = s\<close> |
  \<open>ffold f (Insert x xs) s = ffold f xs (f x s)\<close>
(*-------------------------*)


datatype trm
  = Var nat
  | Const nat
  | Fun nat \<open>trm list\<close>

datatype clause_elem
  = Lit bool nat \<open>trm list\<close>
  | Mat \<open>mat_elem fset\<close>
and mat_elem
  = Cls nat \<open>clause_elem fset\<close>

primrec fimage_clause where \<open>fimage_clause f (idC,C) = (idC,fimage f C)\<close>

fun clause_elem_size and mat_elem_size where
  \<open>clause_elem_size (Lit _ _ _) = 1\<close> |
  \<open>clause_elem_size (Mat \<lbrace>\<rbrace>) = 1\<close> |
  \<open>clause_elem_size (Mat (Insert C Cs)) = 1 + mat_elem_size C + clause_elem_size (Mat Cs)\<close> |
  \<open>mat_elem_size (Cls _ \<lbrace>\<rbrace>) = 1\<close> |
  \<open>mat_elem_size (Cls idC (Insert M Ms)) = 1 + clause_elem_size M + mat_elem_size (Cls idC Ms)\<close>

lemma ignore_id: \<open>mat_elem_size (Cls id1 C) = mat_elem_size (Cls id2 C)\<close> 
  by (induct C) simp_all

primrec substitute where
\<open>substitute \<sigma> (Var i) = Var (\<sigma> i)\<close> |
\<open>substitute \<sigma> (Const i) = Const i\<close> |
\<open>substitute \<sigma> (Fun i ts) = Fun i (map (substitute \<sigma>) ts)\<close>

definition 
\<open>compliment \<sigma> pol pred trms pol' pred' trms' \<equiv>
  (pol \<longleftrightarrow> \<not>pol') \<and> pred = pred' \<and> (map (substitute \<sigma>) trms  = map (substitute \<sigma>) trms')\<close>

fun mat_in_clause and mat_in_mat where
  \<open>mat_in_clause M (Cls _ \<lbrace>\<rbrace>) = False\<close> |
  \<open>mat_in_clause M (Cls idC (Insert M' Ms)) = 
    (M = M' \<or> mat_in_mat M M' \<or> mat_in_clause M (Cls idC Ms))\<close> |
  \<open>mat_in_mat M (Lit _ _ _) = False\<close> |
  \<open>mat_in_mat M (Mat \<lbrace>\<rbrace>) = False\<close> |
  \<open>mat_in_mat M (Mat (Insert C Cs)) = ((mat_in_clause M C) \<or> (mat_in_mat M (Mat Cs)))\<close>

fun clause_in_mat and clause_in_clause where
  \<open>clause_in_mat C (Lit _ _ _) = False\<close> |
  \<open>clause_in_mat C (Mat \<lbrace>\<rbrace>) = False\<close> |
  \<open>clause_in_mat C (Mat (Insert C' Cs)) = 
    (C = C' \<or> clause_in_clause C C' \<or> clause_in_mat C (Mat Cs))\<close> |
  \<open>clause_in_clause C (Cls _ \<lbrace>\<rbrace>) = False\<close> |
  \<open>clause_in_clause C (Cls idC (Insert M Ms)) = 
    (clause_in_mat C M \<or> clause_in_clause C (Cls idC Ms))\<close>

lemma \<open>clause_in_clause C' (Cls idC C) \<longrightarrow> (\<exists> M. C' |\<in>| M \<and> mat_in_clause (Mat M) (Cls idC C))\<close>sorry

function b_clause where
  \<open>b_clause pol pred trms \<lbrace>\<rbrace> = \<lbrace>\<rbrace>\<close> |
  \<open>b_clause pol pred trms (Insert (Lit pol' pred' trms') C) = (
    if pol = pol' \<and> pred = pred' \<and> trms = trms'
    then C
    else Insert (Lit pol' pred' trms') (b_clause pol pred trms C))\<close> |
  \<open>b_clause pol pred trms (Insert (Mat \<lbrace>\<rbrace>) C) = (Insert (Mat \<lbrace>\<rbrace>) C)\<close> |
  \<open>b_clause pol pred trms (Insert (Mat (Insert (Cls idC' C') Cs)) C) = (
    if mat_in_clause (Lit pol pred trms) (Cls idC' C')
    then (Insert (Mat (\<lbrace>(Cls idC' (b_clause pol pred trms C'))\<rbrace>)) C)
    else (Insert (Mat (Insert (Cls idC' C') Cs)) (b_clause pol pred trms C)))\<close> 
  by pat_completeness auto
termination
  apply (relation \<open>measure (\<lambda> (_, _, _, C). mat_elem_size (Cls 0 C))\<close>) 
     apply simp_all
  by (metis add.assoc ignore_id less_SucI less_add_Suc1)

inductive mat_replace where
\<open>\<not> contains_clause_in_mat C M \<Longrightarrow> mat_replace C C' (Mat M) (Mat M)\<close> |
\<open>mat_replace C C' (Lit pol pred trms) (Lit pol pred trms)\<close> |
\<open>C |\<in>| Cs \<Longrightarrow> mat_replace C C' (Mat Cs) (Mat (finsert C' (Cs |-| \<lbrace>C\<rbrace>)))\<close> |
\<open>
  contains_clause_in_mat C M \<Longrightarrow> 
  (Mat M) |\<in>| C'' \<Longrightarrow> (idC'',C'') |\<in>| Cs \<Longrightarrow> 
  mat_replace C C' (Mat M) M' \<Longrightarrow>
  mat_replace C C' 
    (Mat Cs) 
    (Mat (finsert (idC'',finsert M' (C'' |-| \<lbrace>Mat M\<rbrace>)) (Cs |-| \<lbrace>(idC'',C'')\<rbrace>)))\<close>

fun free_vars_trm where
  \<open>free_vars_trm (Var n) = \<lbrace>n\<rbrace>\<close> |
  \<open>free_vars_trm (Const n) = \<lbrace>n\<rbrace>\<close> |
  \<open>free_vars_trm (Fun n trms) = fold (\<lambda> t s. s |\<union>| free_vars_trm t) trms \<lbrace>\<rbrace>\<close>

definition \<open>free_vars_trms trms \<equiv> fold (\<lambda> t s. s |\<union>| free_vars_trm t) trms \<lbrace>\<rbrace>\<close>

abbreviation \<open>contains_var_in_lit_in_clause var pol pred trms C \<equiv>
  var |\<in>| free_vars_trms trms \<and> 
  contains_mat_in_clause (Lit pol pred trms) C\<close>

abbreviation \<open>contains_mat_in_mat M M' \<equiv> 
  (\<exists> C. contains_mat_in_clause (Mat M) C \<and> contains_clause_in_mat C M')\<close>

definition \<open>alpha_related M C pol pred trms \<equiv> 
  (\<exists> M' C1 C2. (contains_mat_in_mat M' M \<or> M' = M) \<and>
  C1 |\<in>| M' \<and> C2 |\<in>| M' \<and> C1 \<noteq> C2 \<and>
  (C = C1 \<or> contains_clause_in_clause C C1) \<and>
  contains_mat_in_clause (Lit pol pred trms) C2)\<close>

definition free_vars_clause where
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

definition \<open>vars_in_mat M \<equiv> THE nset. \<forall> var. var |\<in>| nset \<longleftrightarrow> (\<exists> pol pred trms C idC.
  var |\<in>| free_vars_trms trms \<and> Lit pol pred trms |\<in>| C \<and> contains_clause_in_mat (idC,C) M)\<close>

primrec copy_term where
\<open>copy_term \<delta> (Var i) = Var (\<delta> i)\<close> |
\<open>copy_term \<delta> (Const i) = Const i\<close> |
\<open>copy_term \<delta> (Fun i trms) = Fun i (map (copy_term \<delta>) trms)\<close>

inductive copy_clause_elem where
\<open>copy_clause_elem \<delta> (Lit pol pred trms) (Lit pol pred (map (copy_term \<delta>) trms))\<close> |
\<open>\<forall> C. C |\<in>| M \<longrightarrow> 
  (\<exists> C'. C' |\<in>| M' \<and> C = (idC,C1) \<and> C' = (idC',C2) \<and> idC = idC' \<and>
    (\<forall> cm. cm |\<in>| C1 \<longrightarrow>
    (\<exists> cm'. cm' |\<in>| C2 \<and> copy_clause_elem \<delta> cm cm'
  ))) \<Longrightarrow>
\<forall> C'. C' |\<in>| M' \<longrightarrow> 
 (\<exists> C. C |\<in>| M \<and> C = (idC,C1) \<and> C' = (idC',C2) \<and> idC = idC' \<and>
   (\<forall> cm'. cm' |\<in>| C2 \<longrightarrow>
     (\<exists> cm. cm |\<in>| C1 \<and> copy_clause_elem \<delta> cm cm'
  ))) \<Longrightarrow> 
copy_clause_elem \<delta> (Mat M) (Mat M')\<close>

abbreviation \<open>copy_function \<delta> M C \<equiv> \<forall> var. 
  var |\<in>| vars_in_mat \<lbrace>C\<rbrace> \<longrightarrow> 
  (var |\<in>| free_vars_clause M C \<longrightarrow>
  \<delta> var |\<notin>| vars_in_mat M) \<and>
  (var |\<notin>| free_vars_clause M C \<longrightarrow>
  \<delta> var = var)\<close>

definition \<open>copy_clause \<delta> M C1 C2 \<equiv> 
  copy_function \<delta> M C1 \<and>
  copy_clause_elem \<delta> (Mat \<lbrace>C1\<rbrace>) (Mat \<lbrace>C2\<rbrace>)\<close>

fun snd_fold where
  \<open>snd_fold f (fst',snd') = (fst', fold f snd')\<close>

definition \<open>parent_clause M C \<equiv> THE (idC',C').
  contains_clause_in_mat (idC',C') M \<and> (\<exists> M'. (Mat M') |\<in>| C' \<and> C |\<in>| M')\<close>

definition \<open>extension_clause M P C \<equiv> 
  contains_clause_in_mat C M \<and>
  ((\<exists> pol pred trms. 
    contains_mat_in_clause (Lit pol pred trms) C \<and>
    (pol,pred,trms) |\<in>| P) \<or>
  ((\<forall> pol pred trms C'. 
    (pol,pred,trms) |\<in>| P \<longrightarrow>
    contains_mat_in_clause (Lit pol pred trms) C' \<longrightarrow>
    C' |\<in>| M \<longrightarrow>
    alpha_related M C pol pred trms) \<and>
  (C |\<notin>| M \<longrightarrow> (\<exists> pol pred trms. 
    (pol,pred,trms) |\<in>| P \<and>
    contains_mat_in_clause (Lit pol pred trms) (parent_clause M C)))))\<close>

inductive CC' (\<open>\<turnstile> _ _ _ _\<close> 0) where 
Axiom: \<open>\<turnstile> _ \<lbrace>\<rbrace> _ _\<close> |
Reduction: \<open>
  (\<turnstile> \<sigma> C M (finsert (pol,pred,trms) P)) \<Longrightarrow>
  compliment \<sigma> pol pred trms pol' pred' trms' \<Longrightarrow>
  (\<turnstile> \<sigma> (finsert (Lit pol pred trms) C) M (finsert (pol,pred,trms) P))\<close> |
Extension: \<open>
  (\<turnstile> \<sigma> C M P) \<Longrightarrow>
  copy_clause \<delta> M C1 C2 \<Longrightarrow>
  (mat_replace C1 C2 (Mat M) (Mat M')) \<Longrightarrow>
  (\<turnstile> \<sigma> C3 M' (P |\<union>| \<lbrace>(pol,pred,trms)\<rbrace>)) \<Longrightarrow>
  b_clause (pol,pred,trms) C2 (_,C3) \<Longrightarrow>
  extension_clause M (P |\<union>| \<lbrace>(pol,pred,trms)\<rbrace>) C1 \<Longrightarrow>
  contains_mat_in_clause (Lit pol' pred' trms') C2 \<Longrightarrow>
  compliment \<sigma> pol pred trms pol' pred' trms' \<Longrightarrow>
  (\<turnstile> \<sigma> (C |\<union>| \<lbrace>Lit pol pred trms\<rbrace>) M P)\<close> |
Decomposition: \<open>
  (\<turnstile> \<sigma> (C |\<union>| C') M P) \<Longrightarrow>
  (_,C') |\<in>| M' \<Longrightarrow>
  (\<turnstile> \<sigma> (C |\<union>| \<lbrace>Mat M'\<rbrace>) M P)\<close>

inductive CC where
Start:
\<open>\<turnstile> \<sigma> C2 M \<lbrace>\<rbrace> \<Longrightarrow> copy_clause \<delta> M C1 (_,C2) \<Longrightarrow> contains_clause_in_mat C1 M \<Longrightarrow>
  CC M\<close>

(*Examples*)
lemma \<open>CC \<lbrace>(0,\<lbrace>Lit True 1 []\<rbrace>),(1,\<lbrace>Lit False 1 []\<rbrace>)\<rbrace>\<close>
proof-
  let ?f = \<open>\<lambda> i. i\<close>
  let ?C0 = \<open>(0,\<lbrace>Lit True 1 []\<rbrace>)\<close>
  let ?C1 = \<open>(1,\<lbrace>Lit False 1 []\<rbrace>)\<close>
  let ?M = \<open>\<lbrace>?C0,?C1\<rbrace>\<close>
  have copy_fun: \<open>copy_function ?f ?M ?C0\<close> 
  proof-
    have \<open>vars_in_mat \<lbrace>?C0\<rbrace> = \<lbrace>\<rbrace>\<close>
  have copy1: \<open>copy_clause ?f ?M (0,\<lbrace>Lit True 1 []\<rbrace>) (0,\<lbrace>Lit True 1 []\<rbrace>)\<close> 
  from Start have ?thesis if 
    \<open>\<turnstile> (\<lambda> i. i) \<lbrace>Lit True 1 []\<rbrace> \<lbrace>(0,\<lbrace>Lit True 1 []\<rbrace>),(1,\<lbrace>Lit False 1 []\<rbrace>)\<rbrace> \<lbrace>\<rbrace>\<close>
    using that 

end
