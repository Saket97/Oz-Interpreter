\insert 'Unify.oz'
\insert 'SingleAssignmentStore.oz'

declare Counter MainUtil Main Nop SemanticStack Push Pop IsEmpty SemanticStatement Statement Environment
    Statement = {NewCell nil}
    Environment = {NewCell nil}
    SemanticStack = {NewCell nil}
    Counter = {NewCell 0}
    SemanticStatement = statement(st:Statement env:Environment)

    %Stack Functions
    fun {Pop S} case @S of nil then nil [] X|X1 then S:=X1 X end end
    proc {Push S E} S:=E|@S end
    fun {IsEmpty S} @S==nil end
    %Nop
    proc {Nop}
       {Main}
    end
    
    %This function keeps track of the new variables introduced in SAS. It also ensures that everytime 
    % a unique variable is introduced
    fun {GetNewVar}
       Counter:=@Counter+1
       {AddKeyToSAS @Counter}
       @Counter
    end

    %Returns the copy of the environment with variable N. It takes care of repitions and makes sure to replave them
    % Don't directlt call this function. Use AdjEnv
    fun {CopyEnv L N}
       %{Browse N#L}
       case L of
          nil then N|nil
       [] X|Xr then if X.1==N.1 then {CopyEnv Xr N} else X|{CopyEnv Xr N} end
       end
    end

    % Performs the adj operation on environment. X is the new identifier of the form ident(Z)
    fun {AdjEnv L X}
       %{Browse x#L}
       case X of
          ident(Y) then {CopyEnv L [ident(Y) {GetNewVar}]}
       end
    end

    % Procedure to handle the var command.
    % T = statement(st:[ident(newVariable) <Rest of the statement>] env:E)
    proc {Var T}
        %  {Browse T.st.1#T.st.2.1}
        case T.st of
          nil then {Main}
          [] X|Xr then {Push SemanticStack statement(st:Xr env:{AdjEnv T.env X})} {Main}
        end
    end

    % Procedure to handle the bind command.
    proc {Bind T}
       local X Y in
          X = {FindX T.env T.st.1}
          Y = {FindX T.env T.st.2.1}
          {Browse Y}
          {BindRefToKeyInSAS X Y}
          {Browse X}
       end
    end

    % S = Stack and E = Environment
    proc {MainUtil S E}
	  case S.1 of
          nil then {Main}
          [] nop then {Browse nopMatched#E} {Nop}
          [] var then {Browse var} {Var statement(st:S.2 env:E)}
          [] record then {Browse record}
          [] bind then {Browse bind} {Bind statement(st:S.2 env:E)}
          [] conditional then {Browse conditional}
          [] match then {Browse match}
          [] apply then {Browse apply}
          [] Y|Yr then {Push SemanticStack statement(st:S.2 env:E)} {Push SemanticStack statement(st:S.1 env:E)} {Main}
          end
    end
 
    proc {Main}
      local T in
          T = {Pop SemanticStack}
          case T of
            nil then skip
            [] statement(st:X env:E) then {Browse E} if X==nil then {Main} else {MainUtil X E} end
          end
      end
    end
   
   %{Push SemanticStack statement(st:[[var ident(x) [var ident(y) [var ident(x) [nop]]]][var ident(x) [nop]]] env:nil)}
    {Push SemanticStack statement(st:[var ident(x) [var ident(y) [bind ident(x) ident(y)]]] env:nil)}
    {Main}
    {Browse {Dictionary.items SAS}}
    %{Browse {Dictionary.condGet 
