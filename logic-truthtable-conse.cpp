#include <iostream>
#include <sstream>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <cmath>
#include <ctype.h>

enum
{
    TYPE_EXTERNAL,
    TYPE_DEEP
};

void initInterface();
void deleteSpaces (std::string& expression);
int  parentExcess (const std::string& formula);
bool isValid      (const std::string& expression);
void printTabelaVerdade(std::vector<std::string>& stringList, const std::string formula);
std::string getFormula  ();
std::string encapsule   (std::string formula);
std::string desencapsule(std::string formula, int type);
std::string corrigirStr (std::string formula, bool printResult);
std::vector<std::pair<int, char>> getIndexParenthesis(const std::string& formula);
std::vector<std::pair<int, int>>  expressionIndexes(const std::string& formula);
std::vector<std::string> generateListSub (std::vector< std::pair<int, int> > parentIndexes, const std::string& formulaEnc);
std::vector<std::string> getMainConective(std::string formula);

void initInterface()
{
    std::cout<< "+-------------------------------------------------------------+\n";
    std::cout<< "|             TABELA VERDADE / CONSEQUENCIA LÓGICA            |\n";
    std::cout<< "+-------------------------------------------------------------+\n";
    std::cout<< "|                   Marco Aurelio Lima - 2021                 |\n";
    std::cout<< "+-------------------------------------------------------------+\n";
    std::cout<< " EXEMPLOS: [T.Ver. '(-p#-q)>(-r&-q)']  [C.Log. 'p#q, p>q |- r']\n";
}

void deleteSpaces(std::string& expression)
{
    std::string temp;
    for(auto& i : expression)
    {
        if(i != ' ')
        {
            temp += i;
        }
    }

    expression = temp;
}


int parentExcess(const std::string& formula)
{
    // No caso de "(a)"
    if(formula.size() == 3)
    {
        if(formula[0] == '(' && isalnum(formula[1]) && formula[2] == ')')
        {
            return 1;
        }
    }

    // Remoção no caso specifico em que a extremidades tem que ser removidas, porem não estao no padrão "((a&b))"
    // como por exemplo: "(a&(c&d))"
    // Este metodo consiste em analizar os indices das subformulas e identificar quantos parenteses
    // que abrem na extremidade esquerda e so acabam na extremidade direira
    // O laço for vai procurar o seguinte padrão: ex.: formula tem 10 caracteres -> "0,9" , "1,8" (significa que os dois ultimos parenteses devem ser deletados)
    std::string                        formulaEnc      = encapsule(formula);
    std::vector< std::pair<int, int> > parentIndexes   = expressionIndexes(formulaEnc);
    int contParentExtremidade = 0;
    for(unsigned j=0; j<formulaEnc.size(); j++)
    {
        // Encerar no primeiro caractere que não seja "("
        if(formulaEnc[j] != '(')
        {
            break;
        }
        for(auto& i : parentIndexes)
        {
            if((unsigned)i.first == j && (unsigned)i.second == formulaEnc.size()-j-1)
            {
                contParentExtremidade++;
            }
        }
    }

    return contParentExtremidade;
}

// Verificar a validade dos parenteses. Quantidade dos parenteses: abertos == fechados.
//Dois ou mais atomos nao podem aparecer juntos sem conectivos entre si.
bool isValid(const std::string& expression)
{
    enum
    {
        ERR_ATOM,              // Atomo fora do internalo a - z
        ERR_ATOM_WT_CONNECT,   // Atomos juntos sem conectivos
        ERR_CONNECT,           // Conectivo fora do padrao: - & # >
        ERR_NUM_PARENTESIS,    // Nº de parentesis abertos diferente do nº de parentesis fechados
        ERR_TWO_NEGATIVES,     // Existem dois conectivos unários de negação; redundancia
        ERR_NEG_PARENT_EXTERN, // Negacao de uma formula com parenteses externos
        ERR_PARENT_EXCESS,     // Excesso de parenteses
        ERR_USE_NEGATIVE,      // Operador de negação usado incorretamente (a-)
        ERR_ATOM_SUBFOR,       // Há alguma subformula vazia sendo ligada por conectivo (faltando atomo ou subf.)
    };
    std::map<std::string, bool> error_list;
    int parentesis_cont[2] = {0, 0};

    // verificar se atomos e conectivos estão dentro do padrão
    for(size_t i=0; i<expression.size(); i++)
    {
        if(isalpha(expression[i]))
        {
            if(expression[i] >= 'a' && expression[i] <= 'z')
            {
                if(i < expression.size()-1)
                {
                    // Dois atomos juntos sem conectivo (qq)
                    if(expression[i+1] >= 'a' && expression[i+1] <= 'z')
                    {
                        error_list["ERR_ATOM_WT_CONNECT"] = true;
                    }
                }

            }
            else
            {
                error_list["ERR_ATOM"] = true;
            }
        }
        else
        {
            if(expression[i] != '&' && expression[i] != '#' && expression[i] != '>' && expression[i] != '-')
            {
                if(expression[i] != '(' && expression[i] != ')' && expression[i] != ',' && expression[i] != '@')
                {
                    error_list["ERR_CONNECT"] = true;
                }
            }
            else
            {
                if(expression[i] == '-' && expression[i+1] == '-')
                {
                    error_list["ERR_TWO_NEGATIVES"] = true;
                }
            }
        }

        // Sequencia do tipo ")q"
        if( expression[i] == ')' && (expression[i+1] >= 'a' && expression[i+1] <= 'z'))
        {
            error_list["ERR_ATOM_WT_CONNECT"] = true;
        }
        // Sequencia do tipo "q("
        if((expression[i] >= 'a' && expression[i] <= 'z') && expression[i+1] == '(')
        {
            error_list["ERR_ATOM_WT_CONNECT"] = true;
        }

        // Sequencia do tipo "(-a)"
        if(expression[i] == '(')
        {
            if(expression[i+1] == '-' && isalnum(expression[i+2]) && expression[i+3] == ')')
            {
                // Excessão ao erro: '((p#q),(p>q))@(-r)'
                // Neste caso o encapsulamento do 2o termo feito por mim
                // ocasiona esse erro. Aqui será a correção.

                // Verificar se é expressao de consequencia logica (|-)
                size_t index = expression.find("@");
                if(index != std::string::npos)
                {

                    std::string subform_Dir = expression.substr(index+1, expression.size()-1);
                    if(subform_Dir.size() > 4)
                    {
                        error_list["ERR_NEG_PARENT_EXTERN"] = true;
                    }
                } else
                {
                    error_list["ERR_NEG_PARENT_EXTERN"] = true;
                }


            }
        }

        // Sequencia do tipo "-)"
        if(expression[i] == '-' && expression[i+1] == ')')
        {
            error_list["ERR_USE_NEGATIVE"] = true;
        }


        if(expression[i] == '(')
        {
            parentesis_cont[0]++;
        }
        if(expression[i] == ')')
        {
            parentesis_cont[1]++;
        }
    }

    if(parentesis_cont[0] != parentesis_cont[1])
    {
        error_list["ERR_NUM_PARENTESIS"] = true;
    }


    //Verificar se existem excesso d parenteses externos
    //A verificação so ocorre se o numero de parenteses estiver correto
    if(parentesis_cont[0] == parentesis_cont[1])
    {
        if(parentExcess(expression) > 1)
        {
            error_list["ERR_PARENT_EXCESS"] = true;
        }
    }

    // Verificar erros de digitação de formula: '(a>)>c' ou (&b)>c'
    // algum atomo ou subformula está faltaando para que o conectivo funcione
    if(expression.find("(>") != std::string::npos ||
       expression.find("(&") != std::string::npos ||
       expression.find("(#") != std::string::npos ||
       expression.find(">)") != std::string::npos ||
       expression.find("&)") != std::string::npos ||
       expression.find("#)") != std::string::npos
    )
    {
        error_list["ERR_ATOM_SUBFOR"] = true;
    }


    if(!error_list.empty())
    {
        std::cout<< "+-------------------------------------------------------------+\n";
        std::cout << "|                     FORMULA INVALIDA                        |\n";
        std::cout<< "+-------------------------------------------------------------+\n\n";
    }

    int err_cont = 0;
    if(error_list["ERR_ATOM"])
    {
        std::cout << " [" << ++err_cont << "]  Algum simbolo atomico esta fora do intervalo [a-z]\n" << std::endl;
    }
    if(error_list["ERR_ATOM_WT_CONNECT"])
    {
        std::cout << " [" << ++err_cont << "]  Algum atomo esta sem conectivo\n" << std::endl;
    }
    if(error_list["ERR_CONNECT"])
    {
        std::cout << " [" << ++err_cont << "]  Algum conectivo esta fora do padrao: \n         & (conjuncao)\n         # (disjuncao)\n         > (implicacao)\n         - (negacao)\n" << std::endl;
    }
    if(error_list["ERR_NUM_PARENTESIS"])
    {
        std::cout << " [" << ++err_cont << "]  Parenteses dispostos incorretamente\n" << std::endl;
    }
    if(error_list["ERR_TWO_NEGATIVES"])
    {
        std::cout << " [" << ++err_cont << "]  Ha conectivos unarios de negacao redundantes (--)\n" << std::endl;
    }
    if(error_list["ERR_NEG_PARENT_EXTERN"])
    {
        std::cout << " [" << ++err_cont << "]  Negacao de uma formula com parenteses externos\n" << std::endl;
    }
    if(error_list["ERR_PARENT_EXCESS"])
    {
        std::cout << " [" << ++err_cont << "]  Ha excesso de parenteses\n" << std::endl;
    }
    if(error_list["ERR_USE_NEGATIVE"])
    {
        std::cout << " [" << ++err_cont << "]  Uso errado do operador de nagacao\n" << std::endl;
    }
    if(error_list["ERR_ATOM_SUBFOR"])
    {
        std::cout << " [" << ++err_cont << "]  Há algum atomo ou subformula faltando na expressao\n" << std::endl;
    }


    bool valid = !(error_list["ERR_ATOM"]              ||
                   error_list["ERR_ATOM_WT_CONNECT"]   ||
                   error_list["ERR_CONNECT"]           ||
                   error_list["ERR_NUM_PARENTESIS"]    ||
                   error_list["ERR_TWO_NEGATIVES"]     ||
                   error_list["ERR_NEG_PARENT_EXTERN"] ||
                   error_list["ERR_PARENT_EXCESS"]     ||
                   error_list["ERR_ATOM_SUBFOR"]       ||
                   error_list["ERR_USE_NEGATIVE"]);

    if(!valid)
    {
        std::cout << "+-------------------------------------------------------------+\n";
    }


    return valid;
}


std::string encapsule(std::string formula)
{
    std::stringstream ss;
    ss << "(" << formula << ")";
    return ss.str();
}


std::string desencapsule(std::string formula, int type)
{
    // se a formula.size() for 1, significa que é um conectivo
    if(formula.size() == 1)
    {
        return formula;
    }

    // Remoção no caso specifico em que a extremidades tem que ser removidas, porem não estao no padrão "((a&b))"
    // como por exemplo: "(a&(c&d))"
    // Este metodo consiste em analizar os indices das subformulas e identificar quantos parenteses
    // que abrem na extremidade esquerda e so acabam na extremidade direira
    // O laço for vai procurar o seguinte padrão: ex.: formula tem 10 caracteres -> "0,9" , "1,8" (significa que os dois ultimos parenteses devem ser deletados)
    std::string                        formulaEnc      = encapsule(formula);
    std::vector< std::pair<int, int> > parentIndexes   = expressionIndexes(formulaEnc);
    int contParentExtremidade = 0;
    for(unsigned j=0; j<formulaEnc.size(); j++)
    {
        // Encerar no primeiro caractere que não seja "("
        if(formulaEnc[j] != '(')
        {
            break;
        }
        for(auto& i : parentIndexes)
        {
            if((unsigned)i.first == j && (unsigned)i.second == formulaEnc.size()-j-1)
            {
                contParentExtremidade++;
            }
        }
    }

    std::stringstream ss;
    for(unsigned i=contParentExtremidade; i<formulaEnc.size()-contParentExtremidade; i++)
    {
        ss << formulaEnc[i];
    }
    formulaEnc = ss.str();


    // Remoção profunda de parenteses: retirar excesso de parenteses internamente em átomos na forma "(a)"
    if(type == TYPE_DEEP)
    {
        std::stringstream ss;
        for(unsigned i=0; i<formulaEnc.size(); i++)
        {
            if(formulaEnc[i] == '(' && isalpha(formulaEnc[i+1]) && formulaEnc[i+2] == ')')
            {
                ss << formulaEnc[i+1];
                i+=2;
            }
            else
            {
                ss << formulaEnc[i];
            }
        }
        return ss.str();
    }

    return formulaEnc;
}


std::vector< std::pair<int, char> > getIndexParenthesis(const std::string& formula)
{
    std::vector< std::pair<int, char> > buffer;

    for(unsigned i=0; i<formula.size(); i++)
    {
        if(formula[i] == '(' || formula[i] == ')')
        {
            buffer.push_back(std::pair<int, char>(i, formula[i]));
        }
    }

    return buffer;
}


std::vector< std::pair<int, int> > expressionIndexes(const std::string& formula)
{
    // Indices reais dos parenteses na string
    std::vector< std::pair<int, char> > parenthesisIndexes = getIndexParenthesis(formula);

    // Pares de indices que indicam o parentese que abre e o respectivo parentese que o fecha;
    std::vector< std::pair<int, int> > indexesPair;
    while(!parenthesisIndexes.empty())
    {
        std::vector< std::pair<int, char> > buffer;
        for(unsigned i=0; i<parenthesisIndexes.size(); i++)
        {
            if(parenthesisIndexes[i].second == '(' && parenthesisIndexes[i+1].second == ')')
            {
                indexesPair.push_back(std::pair<int, int>(parenthesisIndexes[i].first, parenthesisIndexes[i+1].first));
                i++;
            }
            else
            {
                buffer.push_back(parenthesisIndexes[i]);
            }
        }
        parenthesisIndexes = buffer;
    }

    return indexesPair;
}


std::vector<std::string> generateListSub(std::vector< std::pair<int, int> > parentIndexes, const std::string& formulaEnc)
{

    std::vector<std::string> subformulas; /// Não usei map<string> por que ele altera a ordem dos itens quando ordena.
    // Subformulas de um átomo só
    for(unsigned i=0; i<formulaEnc.size(); i++)
    {
        if(isalpha(formulaEnc[i]))
        {
            std::stringstream sub;
            sub << formulaEnc[i];
            subformulas.push_back(desencapsule(sub.str(), TYPE_EXTERNAL));
            // Verificar se tem negação antes do atomo e gerar uma nova subformula
            if(i > 0)
            {
                if(formulaEnc[i-1] == '-')
                {
                    subformulas.push_back("-" + sub.str());
                }
            }
        }
    }

    // Subformulas separadas por parenteses
    for(auto& item : parentIndexes)
    {
        std::string sub = "";
        for(int i=item.first; i<=item.second; i++)
        {
            sub += formulaEnc[i];
        }

        // Verificar se tem negação antes dos parenteses de abertura e gerar uma nova subformula
        if(desencapsule(sub, TYPE_DEEP)[0] == '-')
        {
            subformulas.push_back(desencapsule(desencapsule(sub, TYPE_EXTERNAL).substr(1), TYPE_EXTERNAL));
        }

        subformulas.push_back(desencapsule(sub, TYPE_DEEP));
    }


    std::vector<std::string> subformulasNoRepeat;
    for(unsigned i=0; i<subformulas.size(); i++)
    {
        int rpt = 0;
        for(unsigned j=0; j<subformulasNoRepeat.size(); j++)
        {
            if(subformulas[i] == subformulasNoRepeat[j])
            {
                rpt++;
            }
        }
        if(rpt == 0)
        {
            subformulasNoRepeat.push_back(subformulas[i]);
        }
    }

    return subformulasNoRepeat;
}


std::vector<std::string> getMainConective(std::string formula)
{
    // Dado uma formula proposicional corretamente escrita, o conectivo principal é
    // aquele separa duas quantidades iguais de de parenteses de abertura e fechamento
    // (nenhum lado depende do outro e os parenteses abertos encontram o fechamento no mesmo lado).
    // Se eu testar um conectivo, e em cada lado independente nao sobrar a mesma quantidade de parenteses
    // de abertura e fechamento, este não é o principal. Neste caso, há fechamentos na outra parte, logo
    // as partes não são independentes.
    // EX.: (a#b)>(c) | ["(a"] ["b)(c)"]  => '#' NAO É O PRINCIPAL
    // EX.: (a#b)>(c) | ["(a#b)"] ["(c)"] => '>' NAO É O PRINCIPAL

    formula = encapsule(formula);
    formula = desencapsule(formula, TYPE_EXTERNAL);

    if(formula.size() == 3)
    {
        std::vector<std::string> subFormDecomp;
        subFormDecomp.push_back(std::string(1, formula[0]));
        subFormDecomp.push_back(std::string(1, formula[1]));
        subFormDecomp.push_back(std::string(1, formula[2]));

        return subFormDecomp;
    }

    std::vector<std::string> subFormDecomp;
    for(unsigned i=0; i<formula.size(); i++)
    {
        if(formula[i] == '&' || formula[i] == '#' || formula[i] == '>' || formula[i] == '-' || formula[i] == ',' || formula[i] == '@')
        {
            std::stringstream ssEsq;
            int qtdParentEsq[2] {0,0};
            for(unsigned j=0; j<i; j++)
            {
                ssEsq << formula[j];
                if(formula[j] == '(')
                {
                    qtdParentEsq[0]++;
                }
                else if(formula[j] == ')')
                {
                    qtdParentEsq[1]++;
                }
            }

            std::stringstream ssDir;
            int qtdParentDir[2] {0,0};
            for(unsigned j=i+1; j<formula.size(); j++)
            {
                ssDir << formula[j];
                if(formula[j] == '(')
                {
                    qtdParentDir[0]++;
                }
                else if(formula[j] == ')')
                {
                    qtdParentDir[1]++;
                }
            }

            if(qtdParentEsq[0] == qtdParentEsq[1] && qtdParentDir[0] == qtdParentDir[1])
            {
                subFormDecomp.push_back(desencapsule(ssEsq.str(), TYPE_EXTERNAL));
                subFormDecomp.push_back(std::string(1, formula[i]));
                subFormDecomp.push_back(desencapsule(ssDir.str(), TYPE_EXTERNAL));

                return subFormDecomp;
            }
        }
    }

    return subFormDecomp;
}



std::string corrigirStr(std::string formula, bool printResult = false)
{
    std::string                        formulaEnc      = encapsule(formula);
    std::vector< std::pair<int, int> > parentIndexes   = expressionIndexes(formulaEnc);

    // Procurar por conectivos de negação em casa subformula;
    // [1] Verificar negação nas subformulas com parenteses
    // [2] Verificar negação nos atomos
    // [3] Colocar os atomos sem negação entre parenteses
    // Padrao da string no caso de conectivo de negação: "-p" vira "(0-p)" "p>-(q&s)" vira "

    /// FASE [1] Verificar negação nas subformulas com parenteses
    // Guarda o indice dos parenteses de abertura / fechamento para aberturas com negação
    std::vector< std::pair<int, int> > negativeIndexes;
    for(auto& i : parentIndexes)
    {
        if(i.first-1 == -1){ continue; }

        if(formulaEnc[i.first-1] == '-')
        {
            negativeIndexes.push_back(i);
        }
    }

    std::stringstream ss;
    for(unsigned j=0; j<formulaEnc.size(); j++)
    {
        for(auto& i : negativeIndexes)
        {
            if((int)j==i.first-1)
            {
                ss << "[0";
            }
            else if((int)j==i.second+1)
            {
                ss << "]";
            }
        }
        ss << formulaEnc[j];
    }
    formulaEnc = ss.str();


    /// FASE [2] Verificar negação nos atomos
    ss.str(std::string());
    for(unsigned i=0; i<formulaEnc.size(); i++)
    {
        if(formulaEnc[i] == '-')
        {
            //std::cout << formulaEnc[i] << formulaEnc[i+1] << " " << isalpha(formulaEnc[i+1]) << "\n";
            if(isalpha(formulaEnc[i+1]))
            {
                ss << "{0" << formulaEnc[i] << formulaEnc[i+1] << "}";
                i += 2;
            }
        }
        ss << formulaEnc[i];
    }
    formulaEnc = ss.str();


    /// FASE [3] Colocar os atomos sem negação entre parenteses
    ss.str(std::string());
    for(unsigned i=0; i<formulaEnc.size(); i++)
    {
        if(formulaEnc[i+1] == '>' || formulaEnc[i+1] == '#' || formulaEnc[i+1] == '&')
        {
            if(isalpha(formulaEnc[i]) && !isalpha(formulaEnc[i+2]))
            {
                ss << '{' << formulaEnc[i] << '}';
            }
            else if(!isalpha(formulaEnc[i]) && isalpha(formulaEnc[i+2]))
            {
                ss << formulaEnc[i] << formulaEnc[i+1]  << '{' << formulaEnc[i+2] << '}';
                i+=2;
            }
            else
            {
                ss << formulaEnc[i];
            }
        }
        else
        {
            ss << formulaEnc[i];
        }
    }
    formulaEnc = ss.str();

    if(printResult)
    {
        std::cout << "   [CONVERTIDO] " << desencapsule(ss.str(), TYPE_EXTERNAL)  << "\n\n";
    }

    // Substituir "{}" e "[]" por "()"
    ss.str(std::string());
    for(auto& i : formulaEnc)
    {
        if(i == '{' || i == '[')
        {
            ss << '(';
        }
        else if(i == '}' || i == ']')
        {
            ss << ')';
        }
        else
        {
            ss << i;
        }
    }

    if(printResult)
    {
        std::cout << "   [CONV.FINAL] " << ss.str()  << "\n\n";
    }

    return desencapsule(ss.str(), TYPE_EXTERNAL);
}


std::string getFormula()
{
    std::string f = "";
    std::cout << "\n> Formula: ";
    std::getline(std::cin, f);

    return f;
}


void printTabelaVerdade(std::vector<std::string>& stringList, const std::string formula)
{
    // Ordenar stringList em ordem crescente de complexidade das subformulas
    std::vector<std::string> stringListOrd;
    for(unsigned i=0; stringListOrd.size() != stringList.size(); i++)
    {
        for(unsigned j=0; j<stringList.size(); j++)
        {
            if(stringList[j].size() == i)
            {
                stringListOrd.push_back(stringList[j]);
            }
        }
    }
    stringList = stringListOrd;

    // Criar um vector de vector de int; a primeira posição de cada vector corresponde
    // ao indice da subformula da variável stringList
    std::vector< std::vector<int> > table;

    // Definir o tamanho das colunas da tabela verdade; 2 ^ tableHeight
    int tableHeight = 0;
    for(auto &i : stringList)
    {
        // Cada iteração respresenta uma subformula e por consequencia uma coluna
        table.push_back(std::vector<int>());

        // Se a subformula tem tamanho 1, ele é atomico; a quantidade deles definirá a altura das colunas
        if(i.size() == 1) { tableHeight ++; }
    }

    // A altura da tabela é a (2 ^ tableHeight) + 1,
    // pois a 1o posição será reservada para guardar o indice da stringList
    tableHeight = ((int)pow(2, tableHeight)) + 1;

    for(unsigned i=0; i<table.size(); i++)
    {
        for(int j=0; j<tableHeight; j++)
        {
            if(j==0) { table[i].push_back(i); }
            else     { table[i].push_back(0); }
        }
    }

    // Criar uma variavel para guardar subformulas "corrigidas" com o padrão deste programa
    // este padrão interno serve para encapsular totalmente pedaços da formula no intuito
    // de facilitar a localização do conectivo principal.
    // Vou fazer isso porque eu vou precisar saber o conectivo e também irei comparar com outras subformulas
    std::vector<std::string> stringListCorr;
    for(auto& item : stringList)
    {
        stringListCorr.push_back(corrigirStr(item));
    }


    // [1] Preencher as [formulas atomicas]  com os valores distribuidos de forma padronizada
    // [2] Preencher as [formulas restantes]
    for(unsigned i=0; i<table.size(); i++)
    {
        // Como as formulas atomicas sempre estarão na 1o posição, serão modificadas primeiro
        if(stringList[i].size() == 1)
        {
            bool value = 0;
            for(unsigned j=1; j<table[i].size(); j++)
            {
                table[i][j] = value;
                if((j)%(tableHeight/((int)pow(2,i+1))) == 0)
                {
                    value = !value;
                }
            }
        } else   // Aqui será preenchido o restante; as formulas atomicas já estarão todas preenchidas neste momento
        {
            // Separar as duas formulas e o seu conectivo com a função getMainConective()
            // Em seguida, achar o indice das duas subformulas no vector; depois alterar o valor de acordo com o conectivo
            std::vector<std::string> subFormConnectives = getMainConective(stringListCorr[i]);

            int index_left = -1;
            char connective = subFormConnectives[1][0];
            int index_right = -1;

            for(int j=0; j<(int)stringListCorr.size(); j++)
            {
                if(stringListCorr[j].compare(subFormConnectives[0]) == 0)
                {
                    index_left = j;
                }

                if(stringListCorr[j].compare(subFormConnectives[2]) == 0)
                {
                    index_right = j;
                }
            }


            if(connective == '-')
            {
                // se é conectivo de negação, significa que é da forma (o-q), ou seja, uma subformula atomica negada
                for(unsigned k=1; k<table[i].size(); k++)
                {
                    table[i][k] = !((bool)table[index_right][k]);
                }
            }
            else if(connective == '#')
            {
                for(unsigned k=1; k<table[i].size(); k++)
                {
                    table[i][k] = ((bool)table[index_left][k]) || ((bool)table[index_right][k]);
                }
            }
            else if(connective == '&')
            {
                for(unsigned k=1; k<table[i].size(); k++)
                {
                    table[i][k] = ((bool)table[index_left][k]) && ((bool)table[index_right][k]);
                }
            }
            else if(connective == '>')
            {
                for(unsigned k=1; k<table[i].size(); k++)
                {
                    table[i][k] = !((bool)table[index_left][k]) || ((bool)table[index_right][k]);
                }
            }
        }
    }


    // PRINTAR NA TELA A TABELA VERDADE
    for(int i=0; i<tableHeight; i++)
    {
        // Imprime a primeira linha no padrao +---+-------+
        if(i==0)
        {
            for(unsigned j=0; j<table.size(); j++)
            {
                // Ignorar subformulas com virgula
                if(stringList[j].find(",") != std::string::npos ||
                stringList[j].find("@") != std::string::npos){ continue; }

                if((stringList[table[j][0]]).size()%2==0)
                {
                    std::cout << "+-";
                    for(unsigned k=0; k<((stringList[table[j][0]]).size()/2); k++)
                    {
                        std::cout << "-";
                    }
                    std::cout << "-";
                    for(unsigned k=0; k<((stringList[table[j][0]]).size()/2)-1; k++)
                    {
                        std::cout << "-";
                    }
                    std::cout << "-";
                }
                else
                {
                    std::cout << "+-";
                    for(unsigned k=0; k<(stringList[table[j][0]]).size()/2; k++)
                    {
                        std::cout << "-";
                    }
                    std::cout << "-";
                    for(unsigned k=0; k<(stringList[table[j][0]]).size()/2; k++)
                    {
                        std::cout << "-";
                    }
                    std::cout << "-";
                }
            }
            std::cout << "+" << std::endl;
        }

        for(unsigned j=0; j<table.size(); j++)
        {
            // Ignorar subformulas com virgula
            if(stringList[j].find(",") != std::string::npos ||
            stringList[j].find("@") != std::string::npos){ continue; }

            // Imprime o "cabeçalho", que é a subformula cujo indice é encontrado na posição 0 do table;
            if(i==0)
            {
                std::cout << "| " << stringList[j] << " ";
            }
            else // Imprime o restante dos valores, calculando os seus espaços de identação
            {
                if((stringList[table[j][0]]).size()%2==0)
                {
                    std::cout << "| ";
                    for(unsigned k=0; k<(stringList[table[j][0]]).size()/2; k++)
                    {
                        std::cout << " ";
                    }
                    std::cout << table[j][i];
                    for(unsigned k=0; k<((stringList[table[j][0]]).size()/2)-1; k++)
                    {
                        std::cout << " ";
                    }
                    std::cout << " ";
                }
                else
                {
                    std::cout << "| ";
                    for(unsigned k=0; k<(stringList[table[j][0]]).size()/2; k++)
                    {
                        std::cout << " ";
                    }
                    std::cout << table[j][i];
                    for(unsigned k=0; k<(stringList[table[j][0]]).size()/2; k++)
                    {
                        std::cout << " ";
                    }
                    std::cout << " ";
                }
            }
        }
        std::cout << "|" << std::endl;

        // Imprime a segunda e a ultima linha no padrao +---+-------+
        if(i==0 || i == tableHeight-1)
        {
            for(unsigned j=0; j<table.size(); j++)
            {
                // Ignorar subformulas com virgula
                if(stringList[j].find(",") != std::string::npos ||
                stringList[j].find("@") != std::string::npos){ continue; }

                if((stringList[table[j][0]]).size()%2==0)
                {
                    std::cout << "+-";
                    for(unsigned k=0; k<((stringList[table[j][0]]).size()/2); k++)
                    {
                        std::cout << "-";
                    }
                    std::cout << "-";
                    for(unsigned k=0; k<((stringList[table[j][0]]).size()/2)-1; k++)
                    {
                        std::cout << "-";
                    }
                    std::cout << "-";
                }
                else
                {
                    std::cout << "+-";
                    for(unsigned k=0; k<(stringList[table[j][0]]).size()/2; k++)
                    {
                        std::cout << "-";
                    }
                    std::cout << "-";
                    for(unsigned k=0; k<(stringList[table[j][0]]).size()/2; k++)
                    {
                        std::cout << "-";
                    }
                    std::cout << "-";
                }
            }
            std::cout << "+" << std::endl;
        }
    }


    if(formula.find("|") == std::string::npos)
    {
        // Definir a classificação da fórmula ([satisfazivel]  [valida]  [insatisfazivel]  [falsificavel])
        bool satisfazivel = false, falsificavel = false, valida = false,  insatisfazivel = false; int cont = 0;
        for(unsigned i=1; i<table[table.size()-1].size();i++)
        {
            if(!satisfazivel) { satisfazivel =  ((bool)table[table.size()-1][i]); }
            if(!falsificavel) { falsificavel = !((bool)table[table.size()-1][i]); }
            if(table[table.size()-1][i]) { cont++; }
        }

        valida = (cont == (int)table[table.size()-1].size()-1);
        insatisfazivel =  (cont == 0);

        std::cout << "Classificacao: ";
        if(satisfazivel)   { std::cout << " [satisfazivel] ";       }
        if(valida)         { std::cout << " [valida(tautologia)] "; }
        if(insatisfazivel) { std::cout << " [insatisfazivel] ";     }
        if(falsificavel)   { std::cout << " [falsificavel] ";       }
        std::cout<<std::endl;

    } else
    {
        // Separar o lado esquerdo do lado direito
        std::string lado_esq = "";
        std::string lado_dir = "";

        bool control = false;
        for(unsigned i=0;i<formula.size();i++)
        {
            if(formula[i] == '|' && formula[i+1] == '-'){
                control = true;
                i++;
                continue;
            }
            if(!control) { lado_esq += formula[i]; }
            else { lado_dir += formula[i]; }
        }

        // Separar todas as formulas em um vector de string
        std::vector<std::string> conj_formulas;
        std::stringstream ss;
        for(unsigned i=0;i<lado_esq.size();i++)
        {
            if(lado_esq[i] == ',')
            {
                conj_formulas.push_back(ss.str());
                ss.str("");
                continue;
            }

            ss << lado_esq[i];

            if(i == lado_esq.size()-1)
            {
                conj_formulas.push_back(ss.str());
                ss.str("");
            }
        }

        conj_formulas.push_back(lado_dir);

        // Verificar a consequencia logica
        bool conseq_logica = false;

        // A variavel table_temp irá guardar a sequencia da tabela verdade que nos interessa
        // para descobrir se é uma consequencia logica.
        // A ultima posição é a consequencia.
        std::vector< std::vector<int> > table_temp;
        for(unsigned i=0;i<conj_formulas.size();i++)
        {
            for(unsigned j=0;j<stringList.size();j++)
            {
                if(conj_formulas[i].compare(stringList[j]) == 0)
                {
                    table_temp.push_back(table[j]);
                }
            }
        }

        for(int i=1;i<tableHeight;i++)
        {
            int soma_logica = 0;
            for(unsigned j=0;j<table_temp.size()-1;j++)
            {
                soma_logica += table_temp[j][i];
            }

            if(soma_logica  == (int)conj_formulas.size()-1)
            {
                if(table_temp[table_temp.size()-1][i] == 1)
                {
                    conseq_logica = true;
                } else
                {
                    conseq_logica = false;
                    break;
                }
            }
        }

        std::cout << "Conseq. logica: " << ((conseq_logica) ? "[valida]\n" : "[nao-valida]\n");
    }

}



std::string encapsule_conj_formulas(std::string conj_formulas)
{
    // A variavel conj_formulas pode conter uma ou mais formulas
    // Se não houver virgula, simplesmente irá retornar a variavel original.
    // Se houver virgula, vai ser colocado parenteses nos locais corretos

    size_t pos_virg = conj_formulas.find(',');
    size_t pos_simb = conj_formulas.find("|-");

    // Nao tem nem ',' e nem '|-'
    if((pos_virg == std::string::npos) && (pos_simb == std::string::npos))
    {
        return conj_formulas;
    }
    // encontrou apenas ',' e nao '|-'
    if((pos_virg != std::string::npos) && (pos_simb == std::string::npos))
    {
        printf("Erro no conj de formulas.\n");
        return "";
    }
    // encontrou apenas '|-' e nao ','
    if((pos_virg == std::string::npos) && (pos_simb != std::string::npos))
    {
        std::stringstream ss;
        for(unsigned i=0;i<conj_formulas.size();i++)
        {
            if(i==0){ ss << "("; }
            if(i == pos_simb){ ss << ")@("; i++; continue; }
            ss << conj_formulas[i];
            if(i==conj_formulas.size()-1){ ss << ")"; }
        }

        return ss.str();
    }

    // encapsular as virgulas em camadas ex.: (((((a&b)),(c>d)),b) |- (c&d))
    std::stringstream ss_1;
    int cont_parent = 0;
    for(unsigned i=0;i<conj_formulas.size();i++)
    {
        if(conj_formulas[i] == ',')
        {
            if(cont_parent > 0){ ss_1 << ")"; }
            ss_1 << ")" << conj_formulas[i] << "(";
            cont_parent++;
            continue;
        }
        ss_1 << conj_formulas[i];
    }

    std::stringstream ss_2;
    for(int i=0;i<cont_parent+1;i++){ ss_2 << "("; }

    pos_simb = ss_1.str().find("|-");
    for(unsigned i=0;i<ss_1.str().size();i++)
    {
        if(i == pos_simb){ ss_2 << "))@("; i++; continue; }
        ss_2 << ss_1.str()[i];
        if(i == ss_1.str().size()-1){ ss_2 << ")"; }
    }


    return ss_2.str();
}

int main()
{
    initInterface();

    for(;;)
    {
        // Formula com erros:  ((((a*T)>(--cd-))>(-g))) // ((((a*T)>(--cd-))>(-g))
        // Tautologias:        ((p>q)&(p>r))>(p>r)      // (p&q)>p
        // T.Verdade p/ Teste: (-p#-q)>(-r&-q)          // (a#(b&c))>d    // (p#-q)>(r&-q) //  (p&(k#q))>((-j>c)&t) // ((p&q)&((x&y)#s))>(-(v#k)) ;
        // C.Logica  p/ Teste: p#q, p>q |- r            // p#q |- p&q     // p&q |- p#q    //  p#q, p>r, q>r |- r;
        std::string f = getFormula();

        deleteSpaces(f);
        std::string formula = encapsule_conj_formulas(f);

        if(!isValid(formula)){ continue; }

        std::string                        formulaEnc      = encapsule(formula);
        std::vector< std::pair<int, int> > parentIndexes   = expressionIndexes(formulaEnc);
        std::vector<std::string>           subformulasList = generateListSub(parentIndexes, formulaEnc);

        printTabelaVerdade(subformulasList, f);
    }

    return 0;
}
