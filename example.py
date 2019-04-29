import sys
 
l = [n*2 for n in range(10000)] # List comprehension
g = (n for n in range(10000)) # Generator expression
print(type(l))  # <type 'list'>
print(type(g))  # <type 'generator'>
print(sys.getsizeof(l))  # 9032
print(sys.getsizeof(g))  # 80 

print("new")
# firstn with list
def firstn(n):
  num, nums = 0, []
  while num < n:
    nums.append(num)
    num += 1
  return nums

# firstn with generator pattern
class firstn1(object):
  def __init__(self, n):
    self.n = n
    self.num = 0

  def __iter__(self):
    return self

  def __next__(self):
    if self.num < self.n:
      cur, self.num = self.num, self.num + 1
    else:
      raise StopIteration()
    return cur

# firstn generator
def firstn2(n):
  num = 0
  while num < n:
    yield num
    num += 1

l = firstn(10000)
i = firstn1(10000)
g = firstn2(10000)
 
print(type(l))
print(type(i))
print(type(g)) 

print(sys.getsizeof(l))  
print(sys.getsizeof(i)) 
print(sys.getsizeof(g))