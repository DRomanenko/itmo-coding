#include <iostream>
#include <random>
#include <vector>
#include <string>
#include <map>
#include <algorithm>

using namespace std;

const string FILE_NAME_IN = "input";
const string FILE_NAME_OUT = "output";

class Matrix {
private:
    void check_out_of_range(size_t row, size_t col) const {
        if (row >= get_num_rows() || col >= get_num_cols())
            throw out_of_range("");
    }

public:
    vector<vector<bool>> data;

    [[nodiscard]] bool at(size_t row, size_t col) const {
        check_out_of_range(row, col);
        return data[row][col];
    }

    [[nodiscard]] size_t get_num_rows() const {
        return data.size();
    }

    [[nodiscard]] size_t get_num_cols() const {
        return get_num_rows() == 0 ? 0 : data[0].size();
    }

    void sum(size_t row1, size_t row2) {
        for (size_t i = 0; i < data[row1].size() && i < data[row2].size(); ++i)
            data[row1][i] = data[row1][i] ^ data[row2][i];
    }
};

istream &operator>>(istream &stream, Matrix &matrix) {
    int num_rows, num_cols;
    stream >> num_cols >> num_rows;
    matrix = Matrix();
    for (size_t i = 0; i < num_rows; ++i) {
        matrix.data.emplace_back();
        for (size_t q = 0; q < num_cols; ++q) {
            bool value;
            stream >> value;
            matrix.data[i].push_back(value);
        }
    }
    return stream;
}

bool scalar_product(const vector<bool> &a, const vector<bool> &b) {
    bool product = false;
    for (size_t i = 0; i < a.size() & i < b.size(); ++i)
        product ^= a[i] & b[i];
    return product;
}

void pref_gauss(Matrix &matrix) {
    size_t start = 0, qty = 0;
    while (start < matrix.get_num_rows() - 1) {
        size_t current = start;
        while (current < matrix.get_num_rows() && !matrix.at(current, qty)) ++current;
        if (current != matrix.get_num_rows()) {
            swap(matrix.data[start], matrix.data[current]);
            for (size_t i = start + 1; i < matrix.get_num_rows(); ++i)
                if (matrix.at(i, qty))
                    matrix.sum(i, start);
            ++start;
        }
        ++qty;
    }
}

void post_gauss(Matrix &matrix) {
    size_t start = matrix.get_num_cols() - 1, qty = 0;
    vector<bool> used = vector<bool>(matrix.get_num_rows(), false);
    while (qty < matrix.get_num_rows()) {
        long long current = matrix.get_num_rows() - 1;
        while ((current >= 0 && (!matrix.at(current, start) || used[current]))) current--;
        if (current >= 0) {
            for (long long i = matrix.get_num_rows() - 1; i >= 0; i--) {
                if (matrix.at(i, start) && !used[i] && i != current) {
                    matrix.sum(i, current);
                }
            }
            used[current] = true;
            qty++;
        }
        start--;
    }
}


/*
 * Encode - кодирование указанного информационного вектора в заданном коде.
 */
void encode(const Matrix &matrix, const vector<bool> &params, vector<bool> &ans) {
    for (size_t i = 0; i < matrix.get_num_cols(); ++i) {
        vector<bool> column;
        for (const auto &col: matrix.data)
            column.push_back(col[i]);
        ans.push_back(scalar_product(column, params));
    }
}

struct Node {
    bool edge{};
    Node *prev_node = nullptr;
    map<bool, Node *> children = {{false, nullptr},
                                  {true,  nullptr}};
    double diff = -1;

    void add_edge(vector<map<vector<bool>, Node *>> *graph,
                  size_t index,
                  const vector<bool> &column,
                  const vector<bool> &decoded,
                  const vector<bool> &prev_decoded) {
        if (!graph->at(index + 1).count(decoded)) graph->at(index + 1).emplace(decoded, new Node());
        vector<bool> concat_vector = decoded;
        for (size_t i = 0; i < concat_vector.size() && i < prev_decoded.size(); ++i)
            concat_vector[i] = concat_vector[i] | prev_decoded[i];
        this->children[scalar_product(concat_vector, column)] = graph->at(index + 1)[decoded];
    }
};


/*
 * Decode — декодирование указанного вектора в заданном коде.
 * В случае жесткого декодирования оно должно производиться в метрике Хемминга, при этом элементы указанного вектора
 * должен рассматриваться как принадлежащие соответствующему конечному полю.
 *
 * В случае мягкого декодирования элементами входного вектора являются логарифмические
 * отношения правдоподобия L_i = ln{ P(c_i=0|y_i) / P (c_i=1| y_i) }.
 *
 * В выходном файле должно быть представлено восстановленное кодовое слово, список кодовых слов, разделенных
 * запятыми, или сообщение ERROR в случае невозможности декодирования.
 *
 * по алгоритму Витерби: Для каждой вершинки найти минимальную метрику (или максимум функции правдоподобия) пути до неё.
 * Восстановить путь от конечной до начальной вершинки.
 */
void decode(vector<map<vector<bool>, Node *>> *graph, const vector<double> &params, vector<bool> &ans) {
    // очищаем diff следующего слоя
    for (auto const &pair: graph->at(0)) pair.second->diff = 0;
    for (size_t i = 0; i < params.size(); ++i) {
        for (const auto &item: graph->at(i + 1)) item.second->diff = -1;
        // проходимся по всем нодам этого слоя
        for (const auto &item: graph->at(i)) {
            /* биты мы берем в 1 - 2x, т.е. 0(false) станет 1
             * поэтому abs(1 - params[i]), а 1(true) станет -1 поэтому abs(1 - params[i])
             * Идем по ребру 0. Считаем новый diff и устанавливаем его, если он меньше или если в эту ноду его не устанавливали
             */

            // Манхэттенская метрика
            Node *node = item.second->children.at(false);
            if (node) {
                double diff = item.second->diff + abs(1 - params[i]);
                if (node->diff < 0 || diff < node->diff) {
                    node->edge = false;
                    node->prev_node = item.second;
                    node->diff = diff;
                }
            }
            // Тоже самое про 1
            node = item.second->children.at(true);
            if (node) {
                double diff = item.second->diff + abs(-1 - params[i]);
                if (node->diff < 0 || diff < node->diff) {
                    node->edge = true;
                    node->prev_node = item.second;
                    node->diff = diff;
                }
            }
        }
    }
    // Здесь просто берем ребро и вершину из которой пришли, сохранием и идем рекурсивно до начала
    for (auto const &item: graph->back()) {
        // Здесь всего одна нода, которую надо достать как-то (потому что последний слой).
        // Кстати при некорректных данных на последнем слое может быть больше 1 ноды,
        // а именно когда в минимальной спэновой форме есть строка 0 0 0 0 … 0 0 0 1
        Node *node = item.second;
        while (node) {
            ans.push_back(node->edge);
            node = node->prev_node;
        }
    }
    ans.pop_back();
    // Затем переворачиваем результат, потому что он идет в обратном порядке
    reverse(ans.begin(), ans.end());
}


// Структура для решетки - vector<map<vector<bool>, Node *>>
/*
 * Simulate — моделирование процесса передачи случайных данных в канале с указанным
 * уровнем помех (смысл данного параметра указан в соответствующем задании).
 * Должно быть выполнено NumOfIterations итераций генерация данных-кодирование-зашумление-декодирование
 * или должно быть зарегистрировано MaxErrors ошибок декодирования. В выходном файле должна
 * быть приведена полученная частота ошибок декодирования на кодовое слово.
 *
 * Моделирование следует производить для случая канала с двоичной амплитудноимпульсной модуляцией и аддитивным белым гауссовским шумом.
 */
double simulate(const Matrix &matrix,
                vector<map<vector<bool>, Node *>> *graph,
                size_t num_of_iterations,
                size_t max_errors,
                double sigma) {
    mt19937 get_random((random_device()) ());
    normal_distribution<double> distribution{0, pow(sigma, 0.5)};
    size_t it = 0, errors = 0;
    vector<double> noise_levels;
    vector<bool> generated, encoded, decoded;
    for (; it < num_of_iterations && errors < max_errors; ++it) {
        generated.clear();
        for (size_t i = 0; i < matrix.get_num_rows(); ++i) generated.push_back(get_random() % 2);
        encoded.clear();
        encode(matrix, generated, encoded);
        noise_levels.clear();
        for (auto &&value: encoded)
            noise_levels.push_back((value ? -1 : 1) + distribution(get_random));
        decoded.clear();
        decode(graph, noise_levels, decoded);
        if (encoded != decoded) ++errors;
    }
    return ((double) errors) / ((double) it);
}

int main() {
    freopen((FILE_NAME_IN + ".txt").c_str(), "r", stdin);
    freopen((FILE_NAME_OUT + ".txt").c_str(), "w", stdout);
    ios_base::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    // порождающая матрица G двоичного линейного блокового кода
    Matrix matrix;
    cin >> matrix;
    // n - длина. Длина то что больше, в какое слово мы декодируем.
    // k - размерность. Размерность – то из какого множества кодируем.
    /*
     * 0000 ->00001111 (пример кодирования)
     * 4 – Размерность
     * 8 – Длина
     */
    size_t n = matrix.get_num_cols(), k = matrix.get_num_rows();

    /* Get the minimum spun form */
    /*
     * Строим минимальную Спенову Форму.
     * Спеновая форма - это такая порождающая матрица в форме такой, что все ее начала ненулевых строк и концы
     * ненулевых строк различны.
     */
    Matrix m = matrix;
    /*
     * Условимся, что начала строк должны идти последовательно с увеличением номера строки.
     *
     * Пройдёмся Гауссом - верхним проходом и снизу. Верхний проход упорядочит начала по возрастанию и уникализирует их.
     * А проход снизу вверх сделаем чуть хитрее: будем смотреть сколько в рассмотренном столбцу строк с 1.
     * Если это одна, то будем спокойны, просто помечаем, что строка и столбец теперь зачеркнуты, и переходим к следующем столбцу.
     * Если их больше, то вычитаем из всех, кроме последнего с 1, последний столбец с 1.
     */
    pref_gauss(m);
    post_gauss(m);

    /*
     * 1 - начала активных строк
     * 1 - конец активных строк
     */
    vector<pair<size_t, size_t>> spins;
    for (const auto &col: m.data) {
        size_t start = 0, end = col.size() - 1;
        while (!col[start]) { ++start; }
        while (!col[end]) { --end; }
        spins.emplace_back(start, start < end ? end - 1 : start);
    }

    //  Декодируем все в решетку.
    auto *graph = new vector<map<vector<bool>, Node *>>();
    size_t qty_lines = 0;
    auto init = vector<bool>(m.get_num_rows(), false);
    vector<bool> lines = init;
    graph->push_back({{init, new Node()}});
    for (size_t i = 0; i < m.get_num_cols(); ++i) {
        vector<bool> column;
        for (const auto &col: m.data) column.push_back(col[i]);
        graph->push_back({});
        bool new_line = false;
        if (qty_lines < spins.size() && spins[qty_lines].first == i) {
            new_line = true;
            ++qty_lines;
        }
        for (size_t q = 0; q < qty_lines; ++q) lines[q] = spins[q].first <= i && spins[q].second >= i;
        for (auto const &item: graph->at(i)) {
            vector<bool> next_decoded = item.first;
            for (size_t q = 0; q < next_decoded.size() & q < lines.size(); ++q)
                next_decoded[q] = next_decoded[q] && lines[q];
            item.second->add_edge(graph, i, column, next_decoded, item.first);
            if (new_line) {
                next_decoded[qty_lines - 1] = true;
                item.second->add_edge(graph, i, column, next_decoded, item.first);
            }
        }
    }

    // последовательность |V_i| (0 <= i <= n) — число узлов в решетке на ярусе i.
    for (auto &level_size: *graph)
        cout << level_size.size() << ' ';
    cout << '\n';

    string line;
    while (cin >> line) {
        if ("Encode" == line) {
            vector<bool> inf_vector;
            for (size_t i = 0; i < matrix.get_num_rows(); ++i) {
                bool value;
                cin >> value;
                inf_vector.push_back(value);
            }
            vector<bool> encoded;
            encode(matrix, inf_vector, encoded);
            for (const auto value: encoded)
                cout << value << ' ';
        } else if ("Decode" == line) {
            vector<double> noisy_vector;
            for (size_t i = 0; i < matrix.get_num_cols(); ++i) {
                double value;
                cin >> value;
                noisy_vector.push_back(value);
            }
            vector<bool> decoded;
            decode(graph, noisy_vector, decoded);
            for (const auto value: decoded)
                cout << value << ' ';
        } else if ("Simulate" == line) {
            // Под уровнем шума следует понимать отношение сигнал/шум на бит, выраженное в децибелах.
            double noise_level;
            size_t num_of_iterations, max_errors;
            cin >> noise_level >> num_of_iterations >> max_errors;
            // отношение сигнала к шуму. Вычисляем гауссовский шум
            // дисперсия
            cout << simulate(matrix, graph, num_of_iterations / 3, max_errors,
                             (0.5 * pow(10, -noise_level / 10) * n / k));
        }
        cout << '\n';
    }
    return 0;
}