[
  [0, 100, 50],
  [100, 0, 50],
  [50, 50, 50],
].each do |(r, b, c)|
  50.times do |i|
    name = "problems/#{r}-#{b}-#{c}-#{i}.smt2"
    system("cargo run --bin=gen -- --max-real=#{r} --max-bool=#{b} --num-constraints=#{c} > #{name}")
    status = `z3 #{name}`
    `mv #{name} problems/#{status.strip}-#{r}-#{b}-#{c}-#{i}.smt2`

  end
end
