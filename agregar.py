import sqlite3

# Conectamos a tu base de datos
conexion = sqlite3.connect("rae.db")
cursor = conexion.cursor()

try:
    # Insertamos el nuevo administrador
    cursor.execute("""
        INSERT INTO usuarios (usuario, password, rol) 
        VALUES ('admin3.0', '1234', 'admin')
    """)
    
    # Guardamos los cambios
    conexion.commit()
    print("¡Administrador agregado con éxito!")

except sqlite3.Error as e:
    print(f"Hubo un error: {e}")

finally:
    conexion.close()