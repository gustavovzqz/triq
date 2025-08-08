# Linguagem de Programação

Para começar nossos estudos sobre teoria da computação, vamos partir de uma linguagem de programação bem simples:

1. As variáveis $X_1, ..., X_n$ são ditas variáveis de entrada.
2. As variáveis $Z_1, ..., Z_n$ são ditas variáveis locais.
3. A variável $Y$ é dita variável de saída.

Onde as variáveis não determinadas iniciam com valor nulo.

Dessa forma, podemos pensar um programa P qualquer como:

1. Variáveis de entrada;
2. Variáveis locais;
3. Variável de saída;
4. Um conjunto de instruções com ou sem label.

Onde o conjunto de declarações é formado por:

1. V <- V - 1
2. V <- V + 1
3. V <- V
4. IF V != 0 GOTO L

Onde V é uma variável e L é uma label.

Uma instrução é uma declaração ou [L] segido de uma declaração, onde L é uma label do programa. Um programa é uma lista de instruções.

O estado de um programa é uma lista de equações da forma $V = m$ onde $V$ é uma variável e $m$ é um número, incluindo uma equação para cada variável que ocorre em $P$ e não incluindo duas equações para a mesma variável.

A definição de estado permite que variáveis que não ocorrem nas instruções de P possuam algum valor.Assim, o estado:

$$
X_1 = 4; X_2 = 3; Y = 0
$$

é um estado válido para o programa vazio.

Uma snapshot de P é um par $(i, s)$ onde i está limitado por $1$ e $n + 1$, $n$ é o comprimento do programa e $s$ é um estado de P. O sucessor de uma snapshot $(i, s)$, $(j, t)$ é definido da seguinte maneira por casos:

1. Se a i-ésima instruçẽo de P é V <- V + 1 e $s$ contém a equação $V = m$, então $j = i + 1$ e $t$ é o estado $s$ trocando a equação $V = m$ por $V = m + 1$

2. Se a i-ésima instruçẽo de P é V <- V - 1 e $s$ contém a equação $V = m$, então $j = i + 1$ e $t$ é o estado $s$ trocando a equação $V = m$ por $V = m - 1$, se $m$ diferente de zero e não altera caso $m = 0$

3. A i-ésima instrução é de P é V <- V. Daí, o estado não é alterado e $j = i + 1$

4. A í-ésima instrução de P é IF V != 0 GOTO L. Então o estado $t$ é inalterado e:

    a) Se $s$ contém a equação $V = 0$, então $j = i + 1$

    b) Se $s$ contém a equação $V = m$ com $m$ diferente de 0, então, se há uma instrução com label $L$, $j$ é o menor número tal que a j-ésima instrução de P possui label L. Se não há instrução com label $L$, $j = n + 1$.

Uma computação de P é uma lista de snapshots $s_1, ..., s_k$ de P onde $s_{i+1}$ é o sucessor de $s_i$ e $s_k$ é o estado terminal. Observe que essa definição não restringe $s_1$ para começar na primeira instrução.

## Função Computável 

Seja um programa P e $r_1, ... r_m$ números dados. Formaremos um estado $s$ de P que consiste nas equações:

$$
X_1 = r_1, X_2 = r_2, ..., X_m = r_m, Y = 0
$$

Junto das equações $V = 0$ para qualquer outra variável V em P. Chamaremos isso de estado inicial, e a snapshot $(1, s)$ será a snapshot inicial.

Temos dois casos:

1. Existe uma computação $s_1, ..., s_k$ de P começando com a snapshot inicial. Nesse caso, escrevemos$\psi_p^{(m)}(r_1, ..., r_m)$ para o valor de variável Y na snapshot terminal $s_k$

2. Não existe tal computação, ou seja, temos uma sequência infinita começando do estado inicial. Nesse caso, $\psi_p^{(m)}(r_1, ..., r_m)$ é indefinida.

Para qualquer programa P e qualquer inteiro $m$ positivo, a função $\psi_p^{(m)}(x_1, ..., x_m)$ é dita computada por P. Dado uma função parcial $g$, ela é dita parcialmente computável se existe algum programa que a computa. Ou seja, g é parcialmente computável se existe um programa P tal que

$$
g(r_1, ..., r_m) = \psi_p^{(m)}(r_1, ..., r_m)
$$

A igualdade é um pouco mais complexa, ela diz que os dois lados tem o mesmo valor quando são definidos, mas também diz que quando qualquer um dos lados é indefinido, o outro também é.

A função é dita computável se é parcialmente computável e é total.

## Macros

Seja $f(x_1, ..., x_n)$ alguma função parcialmente computável por um programa P. Seja $Y, X_1, ..., X_n, Z_1, .., Z_k,$ o conjunto de variáveis de P e $E, A_1, ..., A_l$ o conjunto de labels. Também vamos assumir que todas as labels $A_1$ existem no programa, isto é, somente $E$ é a label de saída.

Assim, podemos caracterizar P da seguinte forma:

$$
P = P(Y, X_1, ..., X_n, Z_1, ..., Z_k; E, A_1, ..., A_l)
$$

Podemos representar programas que foram obtidos por P por uma troca de variáveis e labels da seguinte maneira.

$$
Q_m = P(Z_m, Z_{m+1}, ..., Z_{m+n}, Z_{m + n + 1}, ..., Z_{m + n + k}; E_m, A_{m+1}, ..., A_{m + l})
$$

Assim, quando quisermos usar macros como: $W <- f(V_1, ..., V_n)$ basta fazer $Z_m$ <- 0, $Z_{m + 1}$ <- $V_1$, ..., (basta ver o programa acima, o que queremos é garantir o estado inicial de $Q_m$ e depois chamar $Q_m$). Depois que chamar $Q_m$, fazemos $W$ <- $Z_m$.

Para funcionar, $m$ precisa ser um valor grande o suficiente para garantir que nenhuma label ou variável que está na expansão ocorra no programa principal. 
