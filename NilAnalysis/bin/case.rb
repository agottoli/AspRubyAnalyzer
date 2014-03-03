a= 5
def test
   puts "You are in the method"
   yield
   puts "You are again back to the method"
   yield  a
end
test {puts "You are in the block"}