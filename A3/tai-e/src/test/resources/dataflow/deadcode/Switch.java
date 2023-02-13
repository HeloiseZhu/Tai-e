class Switch {
    int unreachableSwitchBranch() {
        int x = 2, y;
        switch (x) {
            case 1:
                y = 100;
                break;
            case 2:
                y = 200;
            case 3:
                y = 300;
                break;
            default:
                y = 666;
        }
        return y;
    }
}