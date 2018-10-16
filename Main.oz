local MainUtil Main Nop SemanticStack Push Pop IsEmpty SemanticStatement Statement Environment in
   Statement = {NewCell nil}
   Environment = {NewCell nil}
   SemanticStack = {NewCell nil}
   fun {Pop S} case @S of X|X1 then S:=X1 X end end
   proc {Push S E} S:=E|@S end
   fun {IsEmpty S} @S==nil end

   fun {Nop}
      {Main}
   end
   
   {Push SemanticStack 5}
   {Push SemanticStack 10}
   {Browse @SemanticStack}
   {Browse {Pop SemanticStack}}
   {Browse {IsEmpty SemanticStack}}

   SemanticStatement = statement(statement:Statement environment:Environment)

   fun {MainUtil S E}
      case S of
	 nop then {Browse nop}
	 var then {Browse var}
	 record then {Browse record}
	 bind then {Browse bind}
	 conditional then {Browse conditional}
	 match then {Browse match}
	 apply then {Browse apply}
	 
   end
   

   fun {Main}
      case {Pop SemanticStack} of
	 nil then nil
	 statement(statement:X environment:E) then {MainUtil X E}
      end
      
   end
   
end
