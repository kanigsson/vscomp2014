package Part is

   type Range_And_Zero is range 0 .. 1000;

   subtype Valid_Range is Range_And_Zero range 1 .. 1000;

   type Subset is array (Valid_Range range <>) of Integer;

   subtype Set is Subset (Valid_Range);

   type Partition is array (Valid_Range) of Range_And_Zero;

   function Refine (A : in out Set; P : Partition; X : Set) return Partition;
   --  P is a partition of A. Return new partition such that each equivalence
   --  class S in A is split into S union X and S without X

end Part;
