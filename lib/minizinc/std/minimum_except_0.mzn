%-----------------------------------------------------------------------------%
% Constrains 'm' to be the minimum of the values in 'x' ignoring 0s
% If all 'x' are 0 then 'm' = 'd'
% Assume |x| > 0 /\ x[i] >= 0 /\ x[i] <= d
%-----------------------------------------------------------------------------%

predicate minimum_except_0(var int: m, array[int] of var int: x, int: d) =
    assert(lb_array(x) >= 0, "minimum_except_0: all values must be >= 0",
    assert(ub_array(x) <= d,
        "minimum_except_0: all values must be <= " ++ show(d),
    
         m = min([x[i] + (d - x[i]) * bool2int(x[i] = 0) | i in index_set(x)])
    ));

%-----------------------------------------------------------------------------%
