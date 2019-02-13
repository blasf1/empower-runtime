class HelloWorld(EmpowerApp):
    def loop(self):
        print("Hello! World.")

def launch(tenant_id, every=5000):
    return HelloWorld(tenant_id=tenant_id, every=every)