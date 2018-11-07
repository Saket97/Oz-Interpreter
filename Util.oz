declare Len ListExist L1SubsetL2 GetIdentRecord ListExistClosure Merge
    fun {Len L}
      case L
      of nil then 0
      [] X|Xr then 1+{Len Xr}
      end
    end

    % Should be used by records only. L is a nested list and X is also a list. It matched the first element of X with the 
    % first element of elements in L
    fun {ListExist L X}
      case L
      of nil then false
      [] X1|Xr then if X1.1==X.1 then true else {ListExist Xr X} end
      end
    end

    fun {L1SubsetL2 L1 L2}
        case L1
        of nil then true
        [] X|Xr then if {ListExist L2 X} then {L1SubsetL2 Xr L2} else false end
        end
    end

    fun {GetIdentRecord L X}
      case L
      of nil then nil
      [] Y|Yr then if Y.1==X then Y.2.1 else {GetIdentRecord Yr X} end
      end 
    end

    % Check whether X exist in L
    fun {ListExistClosure L X}
      case L
      of nil then false
      [] X1|Xr then if X1==X then true else {ListExist Xr X} end
      end
    end
    
    fun {Merge L1 L2}
      case L1
      of nil then L2
      [] X|Xr then X|{Merge Xr L2}
      end
    end