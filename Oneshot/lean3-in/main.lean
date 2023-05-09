-- Insert lean 3 code here.

namespace foo

/-- test -/
@[simp] def foo := 1

theorem foo_eq_one : foo.foo = 1 := 
begin
  have : 1 = 1 := rfl;
  simp [foo.foo, this]
end 

end foo
