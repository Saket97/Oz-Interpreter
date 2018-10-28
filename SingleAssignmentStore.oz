declare SAS BindRefToKey RetrieveFromSAS BindValueToKey AddKeyToSAS
{Dictionary.new SAS}

fun {RetrieveFromSAS X}
   local V in
      V = X
      if V==notFound then
         valueNotFound
      else
        local Y in
            Y = {Dictionary.condGet SAS V none}
            case Y
            of none then valueNotFound
            [] value(Z) then Z 
            [] equivalence(Z) then equivalence(Z)
            [] reference(Z) then {RetrieveFromSAS Z}
            end
        end
      end
   end
end

proc {BindValueToKeyInSAS Key Val}
   local V in
      V = {Dictionary.condGet SAS Key none}
      case V
      of equivalence(X) then {Dictionary.put SAS Key value(Val)}
      [] none then {Exception.'raise' noKey(Key)}
      [] value(U) then if U==Val then skip else {Exception.'raise' alreadyAssigned(Key Val U)} end
      [] reference(X) then {BindValueToKeyInSAS X Val}
      end
   end
end

proc {BindRefToKeyInSAS Key RefKey}
   %{Browse 'Hello'}
   local V in
      V = {Dictionary.condGet SAS Key none}
      case V
      of none then {Exception.'raise' noKey(Key)}
      [] equivalence(X) then {Dictionary.put SAS Key reference(RefKey)}
      end
   end
end

proc {AddKeyToSAS Key}
   local V in
      V = {Dictionary.condGet SAS Key none}
      if V==none then {Dictionary.put SAS Key equivalence(Key)} else {Exception.'raise' alreadyAssigned(Key new V)} end
   end
end

%{AddKeyToSAS 1}
%{AddKeyToSAS 2}
%{BindRefToKeyInSAS 2 1}
%{Browse {Dictionary.items SAS}}
