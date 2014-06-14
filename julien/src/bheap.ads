with Ada.Containers.Formal_Vectors;

package BHeap with SPARK_Mode is

   BHeap_Max_Nodes : constant Ada.Containers.Count_Type := 4096;

   type Node_Key is new Ada.Containers.Count_Type range 0 .. BHeap_Max_Nodes;
   type Valid_Node_Key is new Node_Key range Node_Key'First + 1 .. Node_Key'Last;

   Empty_Node : constant Node_Key := 0;

   type Binomial_Heap_Node is record
      Key : Node_Key;
      Degree : Integer;
      Parent : Node_Key;
      Sibling : Node_Key;
      Child : Node_Key;
   end record;

   package Node_Sets is new Ada.Containers.Formal_Vectors (Element_Type => Binomial_Heap_Node, Index_Type => Node_Key);

   Nodes : Node_Sets.Vector (BHeap_Max_Nodes) := Node_Sets.Empty_Vector;

   type Binomial_Heap is record
      Size : Ada.Containers.Count_Type;
      Root : Node_Key;
   end record;

   function Reverse_Node (Node : Node_Key; Sibl : Node_Key) return Node_Key;

   procedure Extract_Min (Heap : in out Binomial_Heap; Min : out Binomial_Heap_Node);

end BHeap;
