declare MainUtil Main Nop SemanticStack Push Pop IsEmpty SemanticStatement Statement Environment
   Statement = {NewCell nil}
   Environment = {NewCell nil}
   SemanticStack = {NewCell nil}
   Counter = {NewCell 0}
   fun {Pop S} case @S of X|X1 then S:=X1 X end end
   proc {Push S E} S:=E|@S end
   fun {IsEmpty S} @S==nil end

   proc {Nop}
      {Main}
   end

   SemanticStatement = statement(st:Statement env:Environment)

   proc {MainUtil S E}
      {Browse func#S}
	 case S of
	 nil then {Main}
	 [] nop then {Browse "NOP"} {Nop}
	 [] var then {Browse var}
	 [] record then {Browse record}
	 [] bind then {Browse bind}
	 [] conditional then {Browse conditional}
	 [] match then {Browse match}
	 [] apply then {Browse apply}
	 [] Y|Yr then {Push SemanticStack statement(st:Yr env:nil)} {Push SemanticStack statement(st:Y env:nil)} {Main}
	 end	 
   end
 
   proc {Main}
      local T in
	 T = {Pop SemanticStack}
	 case T of
	    nil then skip
	    [] statement(st:X env:E) then {MainUtil X E}
	 end
      end
   end

   {Push SemanticStack statement(st:[[nop] [nop] [nop]] env:nil)}
   {Main}