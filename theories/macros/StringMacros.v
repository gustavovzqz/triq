Module Type TStringMacros.

    Parameter program : StringLang.program.

    Parameter max_char : nat.

    Parameter max_z : nat.
    Parameter min_z : nat.

    
    Parameter max_label : nat.
    Parameter min_label : nat.


    (* Propriedades: 
        1. Todas as variáveis são menores que ou iguais a max_z 
        2. ... maiores ...  min_z
        3. Todas as labels são menores que ou iguais a max_label 
        4. ... maiores ... min_label *)

End TStringMacros.

(* Como o livro faz? 
    1. Macro é uma função de variáveis e labels 
       P(Y, X1, X2, ..., Z1, ..., Zk; E, A1, ..., An)
    2. Para obter e inserir a macro dentro do programa,
       fazemos um shift das variáveis e labels do programa
       usando a informação do que já usamos até agora.
    3. Para expandir a macro,
       *)

(* Como expandir macros com labels? 
   A macro é um programa, sua expansão inclui:
    - Transferência de onde está o resultado para onde você quer
    - A label

 Posso simplificar, para incluir reaproveitamento de variáveis SE
 a macro cuidar delas. Caso contrário, preciso seguir a expansão 
 dos livros que cuida das variáveis usadas pela macro (é necessário)
 tomar controle de todas as variáveis
*)