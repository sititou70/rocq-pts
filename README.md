# Rocq PTS

Rocq で Pure Type System（PTS）作ってみる。

- `main.v`：抽象構文（`tm`）、代入（`subst`）、ベータ簡約（`beta`）、型付け規則（`der`）などを定義
- `term_type_kind.v`: 項、型、カインドの具体例を構成して整理してみる
- `cube.v`：PTS を使って、単純型付きラムダ計算、System F、 $\lambda \underline{\omega}$ 、LF、CC を構築して、例題を証明してみる
- `ch.v`：命題論理や述語論理の例題を CC に CH 対応させて証明してみる

## セットアップ

Ubuntu + VSCode 環境で以下を実行する。

```sh
sudo apt install opam
opam install vsrocq-language-server.2.3.4
code --install-extension "rocq-prover.vsrocq@2.3.4"
```

## 参考文献

- Sørensen, Morten Heine, and Pawel Urzyczyn. Lectures on the Curry-Howard isomorphism. Vol. 149. Elsevier, 2006.
- https://en.wikipedia.org/wiki/Pure_type_system
- https://ncatlab.org/nlab/show/pure+type+system
- [Barendregt, Henk P. "Introduction to generalized type systems." (1991).](https://repository.ubn.ru.nl/bitstream/handle/2066/17240/13256.pdf)
