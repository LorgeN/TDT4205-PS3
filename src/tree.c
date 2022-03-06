#include <vslc.h>

static void node_print(node_t *root, int nesting);
static void simplify_tree(node_t **simplified, node_t *root);
static void node_finalize(node_t *discard);

typedef struct stem_t *stem;
struct stem_t
{
    const char *str;
    stem next;
};
static void
tree_print(node_t *root, stem head);

static void destroy_subtree(node_t *discard);

/* External interface */
void destroy_syntax_tree(void)
{
    destroy_subtree(root);
}

void simplify_syntax_tree(void)
{
    simplify_tree(&root, root);
}

extern bool new_print_style;
void print_syntax_tree(void)
{
    if (new_print_style)
        tree_print(root, 0);
    // Old tree printing
    else
        node_print(root, 0);
}

void node_init(node_t *nd, node_index_t type, void *data, uint64_t n_children, ...)
{
    va_list child_list;
    *nd = (node_t){
        .type = type,
        .data = data,
        .entry = NULL,
        .n_children = n_children,
        .children = (node_t **)malloc(n_children * sizeof(node_t *))};
    va_start(child_list, n_children);
    for (uint64_t i = 0; i < n_children; i++)
        nd->children[i] = va_arg(child_list, node_t *);
    va_end(child_list);
}

static void
tree_print(node_t *root, stem head)
{
    static const char *sdown = " │", *slast = " └", *snone = "  ";
    struct stem_t col = {0, 0}, *tail;

    // Print stems of branches coming further down
    for (tail = head; tail; tail = tail->next)
    {
        if (!tail->next)
        {
            if (!strcmp(sdown, tail->str))
                printf(" ├");
            else
                printf("%s", tail->str);
            break;
        }
        printf("%s", tail->str);
    }

    if (root == NULL)
    {
        // Secure against null pointers sent as root
        printf("─(nil)\n");
        return;
    }
    printf("─%s", node_string[root->type]);
    if (root->type == IDENTIFIER_DATA ||
        root->type == STRING_DATA ||
        root->type == EXPRESSION)
        printf("(%s)", (char *)root->data);
    else if (root->type == NUMBER_DATA)
        printf("(%ld)", *((int64_t *)root->data));
    putchar('\n');

    if (!root->n_children)
        return;

    if (tail && tail->str == slast)
        tail->str = snone;

    if (!tail)
        tail = head = &col;
    else
        tail->next = &col;

    for (int64_t i = 0; i < root->n_children; i++)
    {
        col.str = root->n_children - i - 1 ? sdown : slast;
        tree_print(root->children[i], head);
    }
    tail->next = 0;
}

/* Internal choices */
static void
node_print(node_t *root, int nesting)
{
    if (root != NULL)
    {
        printf("%*c%s", nesting, ' ', node_string[root->type]);
        if (root->type == IDENTIFIER_DATA ||
            root->type == STRING_DATA ||
            root->type == EXPRESSION)
            printf("(%s)", (char *)root->data);
        else if (root->type == NUMBER_DATA)
            printf("(%ld)", *((int64_t *)root->data));
        putchar('\n');
        for (int64_t i = 0; i < root->n_children; i++)
            node_print(root->children[i], nesting + 1);
    }
    else
        printf("%*c%p\n", nesting, ' ', root);
}

static void
node_finalize(node_t *discard)
{
    if (discard != NULL)
    {
        free(discard->data);
        free(discard->children);
        free(discard);
    }
}

static void
destroy_subtree(node_t *discard)
{
    if (discard != NULL)
    {
        for (uint64_t i = 0; i < discard->n_children; i++)
            destroy_subtree(discard->children[i]);
        node_finalize(discard);
    }
}

static void
flatten_0(node_t *root)
{
    node_t **children = root->children;
    node_t *items = children[0];

    root->n_children = items->n_children;
    root->children = items->children;

    items->children = NULL;
    items->n_children = 0;

    free(children);
    node_finalize(items);
}

static void
evaluate_constant(node_t *root)
{
    // Make sure everything is constant
    for (uint64_t i = 0; i < root->n_children; i++)
    {
        if (root->children[i]->type == NUMBER_DATA)
        {
            continue;
        }

        // We can't do anything since one of the values is not a constant
        return;
    }

    long *result = malloc(sizeof(long));
    void *data = root->data;

    long val0 = *((long *)(root->children[0]->data));

    if (data == NULL)
    {
        *result = val0;
    }
    else if (root->n_children == 1)
    {
        if (strcmp(data, "-"))
        {
            // This should never happen. This should always be a unary minus
            printf("Unsupported unary operator");
            exit(EXIT_FAILURE);
        }

        *result = -val0;
    }
    else
    {
        long val1 = *((long *)(root->children[1]->data));

        if (!strcmp(data, "+"))
        {
            *result = val0 + val1;
        }
        else if (!strcmp(data, "-"))
        {
            *result = val0 - val1;
        }
        else if (!strcmp(data, "*"))
        {
            *result = val0 * val1;
        }
        else if (!strcmp(data, "/"))
        {
            *result = val0 / val1;
        }
        else
        {
            // Unknown operator
            printf("Unknown operator");
            exit(EXIT_FAILURE);
        }
    }

    for (uint64_t i = 0; i < root->n_children; i++)
    {
        destroy_subtree(root->children[i]);
    }

    free(root->children);
    free(root->data);

    root->children = NULL;
    root->n_children = 0;
    root->type = NUMBER_DATA;
    root->data = result;
}

static void
simplify_tree(node_t **simplified, node_t *root)
{
    // Made some modifications in the parser.y that accomplishes a lot of this directly.
    // Flattening of lists is handled there instead for a cleaner solution.
    // Some nodes are also directly associated with their parent for simplicity.

    for (uint64_t i = 0; i < root->n_children; i++)
    {
        if (root->children[i] != NULL)
        {
            simplify_tree(&root->children[i], root->children[i]);
        }
    }

    // Flatten the types we don't handle directly in the parser
    if (root->type == PRINT_STATEMENT || root->type == PROGRAM)
    {
        flatten_0(root);
    }
    else if (root->type == EXPRESSION)
    {
        evaluate_constant(root);
    }

    *simplified = root;
}
