{- A lazy subtyping algorithm with union and intersection:

A,B := a | ^a | Int | A -> B | forall a. A | A ∪ B | A ∩ B | ⊤
      | ⊥

t := a | ^a | t1 -> t2 | t1 ∪ t2 | t1 ∩ t2

T ::= . | T, a | T, t1<:^a<:t2 | T, A <: B

Algorithm:

|- T 
------------------------------
|- T , a

|- T , t1 <: t2
------------------------------
|- T , t1 <: ^a <: t1 

|- T 
------------------------------
|- T , Int <: Int  

|- T 
------------------------------
|- T , t <: Top  

|- T 
------------------------------
|- T , Bot <: t  

|- T  /\  a in T
------------------------------
|- T , a <: a

|- T  /\  ^a in T
------------------------------
|- T , ^a <: ^a

|- T, C <: A |- B <: D
------------------------------
|- T , A -> B <: C -> D  

|- T, A <: C 
-----------------
|- T, A & B <: C 

|- T, B <: C 
-----------------
|- T, A & B <: C 

|- T, C <: A |- C <: B
-----------------
|- T, C <: A & B

|- T, A <: C |- B <: C
-----------------
|- T, A ∪ B <: C 

|- T, C <: A
-----------------
|- T, C <: A ∪ B

|- T, C <: B
-----------------
|- T, C <: A ∪ B

|- T, ⊥<:^a<:⊤, [^a/a] B <: C
------------------------
|- T, forall a . B <: C            

|- T, b, A <: C           
-----------------------
|- T, A <: forall b . B            

|- ([^a1->^a2 /+ ^a]_[] (T, ^a1, ^a2)), ^a1->^a2 <: A->B   /\ not monotype (A->B)  
---------------------------------------------------------------------------------------
|- T, ^a <: A->B 

|- ([^a1->^a2 /- ^a]_[] (T, ^a1, ^a2)), A->B <: ^a1->^a2   /\ not monotype (A->B)  
---------------------------------------------------------------------------------------
|- T, A->B <: ^a 

|- ([t /- ^a]_[] T)
-----------------------------
|- T, t<:^a  

|- ([t /+ ^a]_[] T) 
-----------------------------
|- T, ^a<:t

|- ([^b /- ^a]_[] T) /\ ^b in front of ^a
-----------------------------
|- T, ^b<:^a

|- ([^b /+ ^a]_[] T) /\ ^b in front of ^a
-----------------------------
|- T, a^<:^b

--------------
[A /* ^a]_E T
--------------

[A /- ^a]_E (T, t1<:^a<:t2)   = T, reverse E, L∪A<:^a<: R        ^a notin FV(A + E)
[A /+ ^a]_E (T, t1<:^a<:t2)   = T, reverse E, L<:^a<:R∩A         ^a notin FV(A + E)

[A /* ^a]_E (T, t1<:^b<:t2)   = [A /* ^a]_E T, t1<:^b<:t2        ^b notin FV(A + E)
[A /* ^a]_E (T, t1<:^b<:t2)   = [A /* ^a]_{E, t1<:^b<:t2} T      (^b in  FV(A + E)) and ^a notin (L+R)
[A /* ^a]_E (T, a)            = [A /* ^a]_{E} T, a               a notin FV(A+ E) 
[A /* ^a]_E (|- T, B <: C)    = [A /* ^a]_{E} T, B <: C       

-}