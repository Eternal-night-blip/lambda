# 简介
这是Church Lambda演算的模拟器,目前还不可以使用

本项目用Rust语言编写,测试覆盖工具使用grcov.
## 运行测试覆盖
RUSTFLAGS="-Cinstrument-coverage" cargo test
### lcov.info文件以便VScode的Coverage Gutters插件可视化测试覆盖结果
grcov . -s . --binary-path ./target/debug/ -t lcov --branch --ignore-not-existing --excl-start '^(pub(\((crate|super)\))? )?mod \w+_tests' --excl-stop '^}' --ignore="*/tests/*"   -o ./lcov.info
### html测试覆盖文件
grcov . -s . --binary-path ./target/debug/ -t html --branch --ignore-not-existing --excl-start '^(pub(\((crate|super)\))? )?mod \w+_tests' --excl-stop '^}' --ignore="*/tests/*" -o ./target/debug/coverage/

target/debug/coverage/index.html
