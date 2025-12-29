
struct myType {
    int x;
    int y;
};

typedef struct myType myType;
typedef myType *myTypePtr;

int main(void) {

    myType var = { 10, 20 };
    myTypePtr varPtr = &var;

    int sum = var.x + varPtr->y;

    return sum;
}
