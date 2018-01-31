theory PPL_Summer_School_2017
  imports Main
begin
  
(* Pure *)  
  
lemma name: "\<And>P. P \<Longrightarrow> P"
proof-
  fix P
  assume 1: "P"
  show "P" by (rule 1)
qed 
  
lemma name2:
  fixes P shows "P \<Longrightarrow> P"
proof-
  assume 1: "P"
  show "P" by (rule 1)
qed
  
lemma name3:
  fixes P assumes 1: "P" shows "P"
  by (rule 1)
  
lemma mp_Pure:
  "\<And> P Q. P \<Longrightarrow> (P \<Longrightarrow> Q) \<Longrightarrow> Q"
proof-
  fix P Q
  assume 1: "P"
  assume 2: "P \<Longrightarrow> Q"
  show "Q"
    (* by (rule 2, rule 1) *)
  proof (rule 2)
    show "P" by (rule 1)
  qed
qed
  
lemma mp_Pure_short:
  fixes P Q 
  assumes 1: "P"
  assumes 2: "P \<Longrightarrow> Q" shows "Q" by (rule 2, rule 1)
    
(* HOL *)
    
term "True"
term "False"
term "~ x"
term "x \<longrightarrow> y"
term "x \<and> y"
term "\<forall>x :: nat. P x \<or> ~ P x"
  
lemma True_HOL: "True" by (rule HOL.TrueI)
    
lemma "~ False"
  find_theorems "(_ \<Longrightarrow> False) \<Longrightarrow> ~ _"
(* by (rule HOL.notI) *)
proof (rule notI)
  assume 1: "False"
  show "False" by (rule 1)
qed
  
lemma "\<forall>p. p \<longrightarrow> p"
  find_theorems "(\<And>_. _) \<Longrightarrow> \<forall>_. _" 
proof (rule allI) (* by (intro allI impI) *)
  fix p
  show "p \<longrightarrow> p"
  by (rule impI)
qed
  
lemma "\<forall>p q. p \<longrightarrow> (p \<longrightarrow> q) \<longrightarrow> q"
proof (intro allI impI)
  find_theorems "PROP _ \<Longrightarrow> (_ \<longrightarrow> _)"
  fix p q
  assume 1: "p"
  assume 2: "p \<longrightarrow> q"
    have 3: "p \<Longrightarrow> q" using 2 by (elim impE)
    show "q" by (rule 3, rule 1)
qed
    
term my_True
  
definition my_True where "my_True = True"
  
term my_True
  
lemma "my_True = True"
  by (rule my_True_def)
    
lemma "my_True"
  unfolding my_True_def by (rule TrueI)
    
definition my_id where "my_id x = x"
  
lemma "my_id x = x" by (rule my_id_def)
    
lemma "my_id (my_id x) = x"
  unfolding my_id_def by (rule refl)
    
lemma "my_id (my_id x) = x" by (simp add: my_id_def)
    
declare my_id_def[simp]
  
definition my_id2 where "my_id2 = (\<lambda>x. x)"
  
declare my_id2_def[simp]
  
(* lemma "my_id = my_id2" 
  unfolding my_id_def my_id2_def by (rule refl) *)
  
lemma "my_id = my_id2" 
  by auto
   
(* List *)
    
term "[]"
term "x#xs"
  
value "[1::int, 2, 3, 4] ! 6"
  
definition my_sorted (* :: "int list \<Rightarrow> bool" *)
  where "my_sorted xs = (
    \<forall> i j. i < j \<longrightarrow>  j < length xs
    \<longrightarrow> ~ (xs!i > xs!j))"
    
lemma my_sortedI [intro]:
  (* fixes xs *)
  assumes 1: "\<And> i j. i < j \<Longrightarrow> j < length xs \<Longrightarrow>
     ~ (xs!i > xs!j)"
  shows "my_sorted xs"
  unfolding my_sorted_def
  using 1 by auto
    
lemma my_sortedD [dest]:
  fixes xs
  assumes 1: "my_sorted xs"
  shows "\<And>i j. i < j \<Longrightarrow> j < length xs \<Longrightarrow> 
        ~ (xs!i > xs!j)"
  using 1 unfolding my_sorted_def by auto
    
lemma my_sortedE [elim]:
  fixes xs
  assumes 1: "my_sorted xs"
  assumes 2: "(\<And>i j. i < j \<Longrightarrow> j < length xs \<Longrightarrow> 
              ~ (xs!i > xs!j)) \<Longrightarrow> P"
  shows "P"
  using 1 2 unfolding my_sorted_def by auto
    
fun my_insert (* :: "int \<Rightarrow> int list \<Rightarrow> int list" *)
  where "my_insert x [] = [x]"
  |     "my_insert x (y#ys) = 
        (if x \<le> y then x # y # ys 
         else y # my_insert x ys)"
    
fun my_sort (* :: "int list \<Rightarrow> int list" *)
  where "my_sort [] = []"
  |     "my_sort (x#xs) = my_insert x (my_sort xs)"
      
value "my_sort [1::int,5,3,8]"
  
value "my_sort [1,5,8,3::int]"
    
value "my_sort [3,7,5,1,9]"
  
term "set xs"
  
lemma my_sorted_Cons' [simp]:
  assumes 1: "my_sorted xs"
  assumes 2: "\<And>y. y \<in> set xs \<Longrightarrow> ~ (x > y)"
  shows "my_sorted (x#xs)" 
proof (rule my_sortedI)
  fix i j :: "nat"
  assume 3: "i < j"
  assume 4: "j < length (x#xs)"
  show "~ ((x # xs) ! i > (x # xs) ! j)"
    
  proof (cases i) 
    case 0
    then show ?thesis using 1 2 3 4 by auto
  next
    case (Suc nat)
    then show ?thesis using 1 2 3 4 by auto
  qed
qed 
  
lemma my_sorted_Cons [simp]:
  "my_sorted (x#xs) \<longleftrightarrow> 
   my_sorted xs \<and> (\<forall>y \<in> set xs. ~ (x > y))"
proof (intro iffI)
  assume 1: "my_sorted xs \<and> (\<forall>y \<in> set xs. ~ (x > y))"
  show "my_sorted (x#xs)"
    using 1 by (intro my_sorted_Cons', auto)
next
  assume 1: "my_sorted (x#xs)"
  show "my_sorted xs \<and> (\<forall>y \<in> set xs. ~ (x > y))"
  proof (intro conjI)
    show "my_sorted xs" (* using 1 by blast *)
      apply (intro my_sortedI) 
      using "1" sorted_nth_monoI by auto
  next
    show "\<forall>y \<in> set xs. ~ (x > y)"
    proof (intro ballI)
      fix y
      assume 2: "y \<in> set xs"
      obtain i where 3: "xs ! i = y" and 4: "i < length xs"
        by (meson "2" in_set_conv_nth)
        
      show "~ (x > y)" 
        using 1 2 3 4 by auto
    qed
  qed
qed     
  
lemma set_my_insert [simp]: 
  "set (my_insert x xs) = set xs \<union> {x}"
by (induct xs, auto)
  
lemma my_sorted_my_insert [intro]:
  fixes xs :: "('a ::preorder) list"
  assumes 1: "my_sorted xs"
  shows "my_sorted (my_insert x xs)"
  using 1 
  apply (induct xs, auto)
  apply (simp add: less_le_not_le)
  apply (meson less_le_trans)
  by (simp add: less_imp_le)
    
theorem my_sorted_my_sort:
  fixes xs :: "('a :: preorder) list"
  shows "my_sorted (my_sort xs)"
by (induct xs, auto)

corollary 
  fixes xs :: "int list"
  shows "my_sorted (my_sort xs)"
  by (rule my_sorted_my_sort)
    
export_code my_sort in OCaml
export_code my_sort in Haskell
  
definition my_sort_integer :: 
  "integer list \<Rightarrow> integer list"
  where "my_sort_integer = my_sort"
    
export_code my_sort_integer in OCaml
export_code my_sort_integer in Haskell
  
instantiation char :: ord
begin
definition less_eq_char where
  "less_eq_char a b = (nat_of_char a \<le> nat_of_char b)"
definition less_char where
  "less_char a b = (nat_of_char a < nat_of_char b)"
instance by (intro_classes)
end
  
declare less_eq_char_def [simp]
declare less_char_def [simp]
  
value "my_sort [CHR ''r'', CHR ''a'', CHR ''b'']

instance char :: lineorder
by (intro_classes, auto)

corollary 
fixes xs :: "char list"
shows "my_sorted (my_sort xs)"
by (rule my_sorted_my_sort)  
 
end